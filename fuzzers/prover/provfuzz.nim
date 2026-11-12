## Soundness fuzzer for Nimony's contract prover (`{.feature: "staticContracts".}`).
##
## A module is 16 independent `p<i>` procs. Each is a statement tree built from
## its own seed, with all locals declared at the top so any statement can be
## deleted (the design of tools/difffuzz.nim). Grammar: ints, `range[0..8]`,
## arrays, seqs, strings, guards in the shapes the prover knows, counting
## `while`/`for` loops, `case` ranges, offset index arithmetic, `var`/`ptr`
## writes, seq mutation, helpers with `.requires`/`.ensures`, `{.assert.}`,
## `{.assume.}`, `try`/`except`, and shared state (globals, a threadvar, `var`
## params that the driver aliases, a captured local, a stashed address) with
## barriers that really write it. Claims come from the guards in scope and are
## then mutated, so true and false claims mix. Flavour A (seed mod 3 == 0)
## names shared state in claims and keeps the constructs of known bugs
## (for+break, negative `shr`, `abs`, `addr`); flavour C (seed mod 3 == 1)
## claims only owned locals and leaves those out: an unsound C finding is new.
##
## Oracle. Mode S compiles with staticContracts; every claim the prover rejects
## is deleted and the module recompiled until it is accepted ("settle"), so what
## is left is exactly what the prover proved. Mode O compiles the same procs
## with runtimeContracts, `range` as `int` and every claim as a run-time test,
## and calls each proc on ~4000 inputs. A proved claim that fails at run time
## is UNSOUND. The original module also runs in mode O: a claim the prover
## called violated that passes is a FALSE-VIOLATION, a "cannot prove" that
## always held goes to incomplete.log. A compiler failure without ordinary
## errors is a CRASH.
##
## Seed mod 3 == 2 is a `func`-rule module instead: 40 routines that each
## write (or return as `var T`) one location along a random access path. The doc
## rule says whether that is legal (in a noSideEffect routine: illegal iff the
## path dereferences a ref/ptr); `nimony check` must agree.
##
## Classifier: an unsound finding's signature is its flavour, claim kind, the
## shared variables the claim names and the known-bug constructs in its proc.
## Reducer: delta debugging over the proc's statement tree (delete subtrees,
## unwrap compound statements, drop else/fuel/ensures), then over
## sub-expressions, while the finding persists.
##
##   nim c -d:release -o:prover/provfuzz prover/provfuzz.nim
##   prover/provfuzz --seed:1 --count:20         # 20 modules
##   prover/provfuzz --seed:1000 --minutes:45    # timed run
##
## Findings (`<kind>_<seed>_<id>.nim/.txt/.reduced.nim`) and log.csv (time_s,
## programs, finding, signature) go to `--out` (default `out/` next to the
## binary); compiles happen in `--work`/w<seed> (default `work/`).

import std / [os, osproc, strutils, random, times, parseopt, tables, algorithm, posix]

type
  ExprKind = enum eLeaf, eBin, eCmp, eAnd, eOr, eNot, eCall, eChk, eTrue, eFalse
  Expr = ref object   ## an expression, kept as a tree so the reducer can shrink it
    kind: ExprKind
    str: string        ## leaf text, operator or callee; eChk: the container
    rhs: string        ## eChk: the "op value" compared with the element
    args: seq[Expr]
    id: int            ## eChk: claim id (a guard that indexes is itself a claim)
  NodeKind = enum nProc, nS, nChk, nIf, nWhile, nFor, nTry, nCase, nOf
  Node = ref object    ## a statement; a proc is the root, every subtree can be deleted
    kind: NodeKind
    fmt: string        ## nS/nChk/nFor: the statement text, `$1..` are `exprs`; nOf: the label
    check: string      ## nChk: assert, assume, idx, pos, between, rng, rnginc, pop
    cont: string       ## nChk: the container (idx, pop) or range variable (rnginc)
    fuel: string       ## nWhile: what to do once out of fuel ("" = a clean loop needs none)
    exprs: seq[Expr]
    kids, els: seq[Node]  ## body and else branch; nCase: kids are the nOf branches
    hasElse: bool
    id: int            ## nChk: claim id; nProc: proc index
    step: int          ## nChk rnginc: the increment
    ensures: Expr      ## nProc: the postcondition, nil = none
    ensId: int         ## nProc: claim id of `ensures`
    flavour: char      ## nProc: 'A' or 'C'
  Line = tuple[text: string, owner, node: Node]  ## a rendered line, its proc and its statement

var
  nimony = "/home/ageralis/Projects/nimony/bin/nimony"
  workDir, outDir: string
  budget = 150
  doReduce = true
  programs = 0       ## procs and routines generated so far
  start = epochTime()

# ---- expressions -------------------------------------------------------------

# Constructors, kept short so the grammar below reads like the code it generates.
proc leaf(s: string): Expr = Expr(kind: eLeaf, str: s)
proc num(k: int): Expr = leaf(if k < 0: "(" & $k & ")" else: $k)
proc bin(op: string; l, r: Expr): Expr = Expr(kind: eBin, str: op, args: @[l, r])
proc cmp(op: string; l, r: Expr): Expr = Expr(kind: eCmp, str: op, args: @[l, r])
proc conj(l, r: Expr): Expr = Expr(kind: eAnd, args: @[l, r])
proc disj(l, r: Expr): Expr = Expr(kind: eOr, args: @[l, r])
proc negate(x: Expr): Expr = Expr(kind: eNot, args: @[x])
proc call(f: string; xs: varargs[Expr]): Expr = Expr(kind: eCall, str: f, args: @xs)

let arrays = {"ar": (0, 7), "la": (2, 5), "o.arr": (0, 3)}.toTable   # fixed-size containers: first, last index
proc loHi(c: string): (Expr, Expr) =
  ## Index bounds of container `c`, `hi` exclusive.
  if c in arrays: (num(arrays[c][0]), num(arrays[c][1] + 1)) else: (num(0), leaf(c & ".len"))
proc inBounds(c: string; e: Expr): Expr =
  let (lo, hi) = loHi(c)
  conj(cmp(">=", e, lo), cmp("<", e, hi))

proc render(e: Expr; oracle: bool): string =
  ## In the oracle an indexing guard reports itself through `ok(id, inBounds)`: it is a claim too.
  template r(i: int): string = render(e.args[i], oracle)
  case e.kind
  of eLeaf: e.str
  of eBin: "(" & r(0) & " " & e.str & " " & r(1) & ")"
  of eCmp: r(0) & " " & e.str & " " & r(1)
  of eAnd: "(" & r(0) & " and " & r(1) & ")"
  of eOr: "(" & r(0) & " or " & r(1) & ")"
  of eNot: "not (" & r(0) & ")"
  of eCall:
    var xs: seq[string]
    for a in e.args: xs.add render(a, oracle)
    e.str & "(" & xs.join(", ") & ")"
  of eTrue: "true"
  of eFalse: "false"
  of eChk:
    let acc = e.str & "[" & r(0) & "] " & e.rhs
    if oracle: "(ok(" & $e.id & ", " & render(inBounds(e.str, e.args[0]), oracle) & ") and " & acc & ")" else: acc

proc condIds(e: Expr): seq[int] =
  if e.kind == eChk: result.add e.id
  for x in e.args: result.add condIds(x)
proc unchecked(e: Expr): Expr =
  ## `e` with its indexing guards replaced by `false` (how settle drops a rejected one).
  if e.kind == eChk: return Expr(kind: eFalse)
  result = Expr(kind: e.kind, str: e.str, rhs: e.rhs, id: e.id)
  for a in e.args: result.args.add unchecked(a)

# ---- statement trees -----------------------------------------------------------

proc walk(n: Node): seq[Node] =
  ## `n` and every node below it, parents first (the reducer indexes nodes by this order).
  result = @[n]
  for c in n.kids & n.els: result.add walk(c)
proc clone(n: Node): Node =
  result = Node()
  result[] = n[]
  result.kids = @[]
  result.els = @[]
  for c in n.kids: result.kids.add clone(c)
  for c in n.els: result.els.add clone(c)
proc splice(l: var seq[Node]; n: Node; by: seq[Node]): bool =
  let j = l.find(n)
  if j >= 0:
    l.delete(j)
    for k, x in by: l.insert(x, j + k)
  j >= 0
proc subst(root, n: Node; by: seq[Node] = @[]): bool =
  ## Replaces `n` by `by` wherever it hangs below `root` (deletes it by default).
  for par in walk(root):
    if splice(par.kids, n, by) or splice(par.els, n, by): return true
proc claims(p: Node): seq[(int, string)] =
  ## Every claim in proc `p` as (id, kind); an assume is not a claim.
  for n in walk(p):
    if n.kind == nChk and n.check != "assume": result.add (n.id, n.check)
    for e in n.exprs:
      for c in condIds(e): result.add (c, "condidx")
  if p.ensures != nil: result.add (p.ensId, "ensures")
proc hasClaim(n: Node; id: int): bool =
  ## Does statement `n` carry claim `id`?
  if (n.kind == nChk and n.id == id) or (n.kind == nProc and n.ensId == id and n.ensures != nil): return true
  for e in n.exprs:
    if id in condIds(e): return true

proc claimed(n: Node): Expr =
  ## The run-time condition a check node claims.
  let x = n.exprs
  case n.check
  of "assert", "assume": x[0]
  of "idx": inBounds(n.cont, x[0])
  of "pos": cmp(">", x[0], num(0))
  of "between": conj(cmp("<=", x[1], x[0]), cmp("<=", x[0], x[2]))
  of "rng": conj(cmp(">=", x[0], num(0)), cmp("<=", x[0], num(8)))
  of "rnginc":
    let e = bin("+", leaf("int(" & n.cont & ")"), num(n.step))
    conj(cmp(">=", e, num(0)), cmp("<=", e, num(8)))
  else: cmp(">", leaf(n.cont & ".len"), num(0))   # pop

# ---- rendering ------------------------------------------------------------------

const
  # `RT` is `range[0..8]` in mode S and `int` in mode O, so an out-of-range value shows at run time.
  Prelude = """
import std/syncio
type
  RT = $1
  Obj = object
    f, g: int
    cnt: RT
    items: seq[int]
    arr: array[4, int]
  B = ref object of RootObj
  D = ref object of B
  Hold = ref object
    o: Obj
proc needsPos(x: int): int {.requires: x > 0.} = x - 1
proc needsRange(x, lo, hi: int): int {.requires: lo <= x and x <= hi.} = x
proc clamp7(x: int): int {.ensures: 0 <= result and result <= 7.} =
  if x < 0: return 0
  if x > 7: return 7
  return x
proc nonNeg(x: int): int {.ensures: result >= 0.} =
  if x < 0: return 0
  return x
proc below(x, lim: int): int {.requires: lim > 0, ensures: 0 <= result and result < lim.} =
  if x < 0: return 0
  if x >= lim: return lim - 1
  return x
proc bump(x: var int) = inc x
proc setTo(x: var int; v: int) = x = v
proc viaPtr(p: ptr int; v: int) = p[] = v
proc shrink(q: var seq[int]) = q.setLen(0)
proc dropOne(q: var seq[int]) =
  if q.len > 0: q.setLen(q.len - 1)
proc clobber(o: var Obj) =
  o.f = o.f * 7 - 3
  o.items.setLen(0)
proc takesRT(x: RT): int = int(x)
var gv = 0
var tv {.threadvar.}: int
var go = Obj()
var gs: seq[int] = @[]
var gp: ptr int = addr gv
var gb: B = B()
proc setGv(v: int) = gv = v
proc bumpGv() = inc gv
proc setTv(v: int) = tv = v
proc touchGo() =
  go.f = go.f * 7 - 3
  go.items.setLen(0)
proc clearGs() = gs.setLen(0)
proc pokeP(v: int) = gp[] = v
proc stash(p: ptr int) = gp = p
method poke(b: B; v: int) {.base.} = gv = v
method poke(d: D; v: int) =
  go.f = v
  tv = v
proc mixG(x: var int) =
  inc x
  gv = gv * 3 + 1
var gfn: proc (v: int) {.closure.} = setTv
func fbump(x: var int) = inc x
func fset(x: var int; v: int) = x = v
func fclob(o: var Obj) =
  o.f = o.f * 5 + 1
  o.items.setLen(0)
func fadd(s: var seq[int]; v: int) = s.add v
proc risky(x: int) {.raises.} =
  if x > 3: raise Failure
"""
  # `bad`/`ok` record a claim. After the first failure the input is `dead`: later claims were proved
  # assuming the failed one, so they say nothing.
  Harness = """
var reached: array[$1, bool]
var failed: array[$1, bool]
var passed: array[$1, bool]
var wit: array[$1, bool]
var dead = false
var lastFail = 0
proc fail(id: int) =
  if not dead:
    failed[id] = true
    lastFail = id
    dead = true
proc bad(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = not c
proc ok(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = c
"""
  Params = "a, b, c: int; u: uint8; s: seq[int]; t: var seq[int]; o: var Obj; ar: array[8, int]; st: string; " &
           "n: var int; q: var Obj"
  # Locals are declared up front so that any statement can be deleted.
  Locals = ["var x = a", "var y = b", "var z = c", "var i = 0", "var j = 0", "var fuel = 0", "var w = u",
            "var r: RT = 0", "var la = default(array[2..5, int])", "result = 0", "var cx = c",
            "proc setCx(v: int) {.closure.} = cx = v", "var fn: proc (v: int) {.closure.} = setCx", "gp = addr gv"]
  # The driver: every proc on ~4000 inputs; `al` picks what `n`/`q` alias (0: nothing, 1: gv and the same
  # object behind two refs, 2: tv and go).
  Driver = """
proc drive$1() =
  var ar = default(array[8, int])
  for k in 0 ..< 8: ar[k] = (k * 5) mod 11 - 2
  var ss = [@[1], @[2], @[0, 5, -1], @[7, 1, 3, 0, 2, 8, 4, 6]]
  ss[0].setLen(0)
  let sts = ["", "a", "abcd", "abcdefgh"]
  for a in [low(int), -9, -1, 0, 1, 2, 5, 7, 8, 9, high(int)]:
    for b in [-1, 0, 1, 2, 3, 4, 6, 7, 8, high(int)]:
      for c in [-1, 2, 9]:
        for u in [0'u8, 7'u8, 255'u8]:
          for si in 0 ..< 4:
            dead = false
            var t = ss[(si + 1) mod 4]
            var o = Obj(f: b, g: c, cnt: (si * 2), items: ss[(si + 2) mod 4])
            gv = b
            tv = c
            go = Obj(f: a and 15, g: b, cnt: si, items: ss[(si + 3) mod 4])
            gs = ss[(si + 2) mod 4]
            gp = addr gv
            gb = (if (si and 1) == 0: B() else: D())
            var nn = c
            var qq = Obj(f: c, g: a, items: ss[(si + 1) mod 4])
            let ha = Hold(o: Obj(f: b, g: c, cnt: (si * 2), items: ss[(si + 2) mod 4]))
            let hb = ha
            let al = $2
            var rr = 0
            if al == 0:
              rr = p$1(a, b, c, u, ss[si], t, o, ar, sts[(si + c + 1) mod 4], nn, qq)
            elif al == 1:
              rr = p$1(a, b, c, u, ss[si], t, ha.o, ar, sts[(si + c + 1) mod 4], gv, hb.o)
            else:
              rr = p$1(a, b, c, u, ss[si], t, o, ar, sts[(si + c + 1) mod 4], tv, go)
$3
            if dead and not wit[lastFail]:
              wit[lastFail] = true
              echo "W ", lastFail, " a=", a, " b=", b, " c=", c, " u=", u, " si=", si
drive$1()
"""
  PostCheck = """
            if not dead:
              reached[$1] = true
              if $2: passed[$1] = true
              else: fail($1)"""
  Tail = """
for i in 0 ..< $1:
  if reached[i]: echo "R ", i
  if passed[i]: echo "P ", i
  if failed[i]: echo "F ", i
"""

proc put(res: var seq[Line]; s: string; p: Node = nil; n: Node = nil) = res.add (text: s, owner: p, node: n)

# Statements under proc `p`, indented by `ind`; each line remembers its proc and node so that an error
# message can be mapped back to the claim it is about.

proc emit(n, p: Node; ind: string; oracle: bool; res: var seq[Line])
proc emitBlock(ns: seq[Node]; p: Node; ind: string; oracle: bool; res: var seq[Line]) =
  if ns.len == 0: res.put(ind & "discard", p)
  for n in ns: emit(n, p, ind, oracle, res)

proc emit(n, p: Node; ind: string; oracle: bool; res: var seq[Line]) =
  var x: seq[string]
  for e in n.exprs: x.add render(e, oracle)
  template line(s: string) = res.put(ind & s, p, n)
  template sub(ns: seq[Node]) = emitBlock(ns, p, ind & "  ", oracle, res)
  case n.kind
  of nS: line(n.fmt % x)
  of nChk:
    if not oracle:
      line(if n.check == "assert": "{.assert: " & x[0] & ".}"
           elif n.check == "assume": "{.assume: " & x[0] & ".}" else: n.fmt % x)
    elif n.check == "assume":   # a false assumption is UB: this input proves nothing from here on
      line("if not (" & render(claimed(n), oracle) & "): (dead = true; return)")
    else:
      line("if bad(" & $n.id & ", " & render(claimed(n), oracle) & "): return")
      if n.check != "assert": line(n.fmt % x)
  of nIf, nTry:
    line(if n.kind == nIf: "if " & x[0] & ":" else: "try:")
    sub(n.kids)
    if n.hasElse:
      res.put(ind & (if n.kind == nIf: "else:" else: "except:"), p)
      sub(n.els)
  of nWhile:
    line("while " & x[0] & ":")
    if n.fuel != "":
      res.put(ind & "  inc fuel", p)
      res.put(ind & "  if fuel > 24: " & n.fuel, p)
    sub(n.kids)
  of nFor:
    line(n.fmt % x)
    sub(n.kids)
  of nCase:
    line("case " & x[0])
    for b in n.kids:
      res.put(ind & "of " & b.fmt & ":", p)
      sub(b.kids)
    res.put(ind & "else:", p)
    sub(n.els)
  of nProc, nOf: discard

proc render(ps: seq[Node]; oracle: bool; nclaims: int): (string, seq[Line]) =
  ## Mode S (staticContracts, claims as pragmas) or, with `oracle`, mode O (claims as run-time tests and
  ## a driver per proc). Returns the text and what each line belongs to.
  var res: seq[Line]
  var hdr = "{.feature: \"" & (if oracle: "runtimeContracts" else: "staticContracts") &
            "\".}\n{.feature: \"assumeSync\".}\n" & Prelude % (if oracle: "int" else: "range[0..8]")
  if oracle: hdr.add Harness % $max(nclaims, 1)
  for l in hdr.strip(leading = false).splitLines: res.put(l)
  for p in ps:
    let pr = if p.ensures != nil and not oracle: " {.ensures: " & render(p.ensures, oracle) & ".}" else: ""
    res.put("proc p" & $p.id & "(" & Params & "): int" & pr & " =", p, p)
    for h in Locals: res.put("  " & h, p)
    emitBlock(p.kids, p, "  ", oracle, res)
    if oracle:
      let post = if p.ensures == nil: "            discard rr"
                 else: PostCheck % [$p.ensId, render(p.ensures, oracle).replace("result", "rr").
                                    replace("s.len", "ss[si].len")]
      let al = if p.flavour == 'C': "0" else: "(si + (c and 3)) mod 3"
      for l in (Driver % [$p.id, al, post]).strip(leading = false).splitLines: res.put(l)
  if oracle:
    for l in (Tail % $max(nclaims, 1)).strip(leading = false).splitLines: res.put(l)
  res.put("echo \"END\"")
  var text = ""
  for l in res: text.add l.text & "\n"
  (text, res)

# ---- generator ------------------------------------------------------------------

const
  Shared = ["gv", "tv", "go.f", "n", "q.f", "cx"]   # what a barrier can change behind the prover's back
  Writable = ["la", "t", "o.items", "o.arr"]        # containers an index statement may store into

type Gen = object
  ## Generator state for one proc; the scope-like fields are cut back at the end of each block.
  rng: Rand
  isA: bool                             ## flavour A: shared state in claims, known-bug constructs on
  lvals: seq[string]                    ## int locations a statement may write
  seqs, growable, conts: seq[string]    ## seqs; those that may grow; anything indexable
  conds: seq[Expr]                      ## guards believed to hold here (invalidation ignored: that is the point)
  guarded, ptrs: seq[(string, string)]  ## (lvalue, container) a guard bounds; (ptr, target)
  lets: seq[string]                     ## `let`s and loop variables in scope
  frozen: seq[string]                   ## must not be written: a clean loop's counter, a C try body
  loops: seq[string]                    ## enclosing loop kinds, innermost last
  nogrow: int                           ## > 0: no seq may grow (inside a clean loop or a C try body)
  tryDepth: int
  uniq: int                             ## counter for fresh names
  ids: int                              ## next claim id, shared by the whole module

proc pick[T](g: var Gen; xs: openArray[T]): T = xs[g.rng.rand(xs.high)]
proc chance(g: var Gen; p: float): bool = g.rng.rand(1.0) < p
proc roll(g: var Gen; m = 1.0): float = g.rng.rand(m)
proc fresh(g: var Gen; pf: string): string =
  inc g.uniq
  pf & $g.uniq
proc newId(g: var Gen): int =
  result = g.ids
  inc g.ids
proc last[T](xs: seq[T]; n: int): seq[T] = xs[max(0, xs.len - n) .. ^1]
proc without(xs, drop: openArray[string]): seq[string] =
  for x in xs:
    if x notin drop: result.add x
proc among(xs, keep: openArray[string]): seq[string] =
  for x in xs:
    if x in keep: result.add x
proc writable(g: Gen): seq[string] = without(g.lvals, g.frozen)
proc simple(fmt: string; ex: varargs[Expr]): Node = Node(kind: nS, fmt: fmt, exprs: @ex)
proc newCheck(g: var Gen; ck: string; ex: seq[Expr]; fmt = ""; cont = ""; step = 0): Node =
  Node(kind: nChk, check: ck, id: g.newId, exprs: ex, fmt: fmt, cont: cont, step: step)

proc atom(g: var Gen): Expr =
  let q = g.roll
  if q < 0.45: leaf(g.pick(g.lvals & @["a", "b", "c", "x", "i"] & g.lets & g.lets))
  elif q < 0.65: num(g.pick([-2, -1, 0, 0, 1, 1, 2, 3, 4, 5, 7, 8, 9, 10]))
  elif q < 0.82: leaf(g.pick(g.seqs & @["st"]) & ".len")
  elif q < 0.90: leaf(g.pick(["int(u)", "int(w)", "int(r)", "int(o.cnt)", "high(s)", "high(t)", "int(u + 1'u8)",
                             "int(w - 1'u8)", "int(w * 2'u8)", "int(u and 7'u8)", "int(u shr 5)"]))
  elif g.ptrs.len > 0 and q < 0.95: leaf(g.pick(g.ptrs)[0] & "[]")
  else: leaf(g.pick(["a", "b", "x", "y"]))

proc intExpr(g: var Gen; d = 2): Expr =
  if d <= 0 or g.chance(0.35): return g.atom
  let q = g.roll
  if q < 0.30: bin(g.pick(["+", "-"]), g.intExpr(d-1), g.pick([num(1), num(1), num(2), g.intExpr(d-1)]))
  elif q < 0.36: bin("*", g.intExpr(d-1), num(g.pick([2, 3, -1])))
  elif q < 0.44: bin("div", g.intExpr(d-1), num(g.pick([2, 3, 4])))
  elif q < 0.52: bin("mod", g.intExpr(d-1), num(g.pick([2, 4, 5, 8])))
  elif q < 0.62: bin("and", g.intExpr(d-1), num(g.pick([1, 3, 7, 7, 15, 255])))
  elif q < 0.68:
    var x = g.intExpr(d-1)
    if not g.isA and x.kind == eLeaf and x.str.startsWith("(-"): x = leaf(x.str[2 .. ^2])  # finding 02
    bin("shr", x, num(g.pick([1, 2, 3])))
  elif q < 0.80: call(g.pick(["min", "max"]), g.intExpr(d-1), g.intExpr(d-1))
  elif q < 0.88: call(g.pick(if g.isA: @["clamp7", "nonNeg", "abs", "abs"] else: @["clamp7", "nonNeg"]), g.intExpr(d-1))
  elif q < 0.93: bin("-", bin("-", leaf(g.pick(g.seqs) & ".len"), num(1)), g.intExpr(d-1))
  else: g.atom

proc small(g: var Gen): Expr =
  ## Bounded and nonnegative: safe as a loop bound.
  let q = g.roll
  if q < 0.45: loHi(g.pick(g.conts))[1]
  elif q < 0.6: num(g.pick([0, 1, 3, 4, 6, 8, 9]))
  elif q < 0.8: bin("and", g.intExpr(1), num(g.pick([3, 7, 15])))
  elif q < 0.9: call("clamp7", g.intExpr(1))
  else: bin("-", loHi(g.pick(g.seqs))[1], num(1))

proc compare(g: var Gen; d = 1): Expr =
  cmp(g.pick(["<", "<=", ">", ">=", "==", "!=", "<", ">="]), g.intExpr(d),
    g.pick([g.intExpr(d), g.atom, num(g.pick([0, 0, 1, 7, 8]))]))

proc guard(g: var Gen; v, c: string): Expr =
  ## `v` against the bounds of `c`, in one of the shapes the prover knows.
  let e = leaf(v)
  let (lo, hi) = loHi(c)
  let q = g.roll
  let lower = g.pick([cmp(">=", e, lo), cmp("<=", lo, e), cmp(">", e, bin("-", lo, num(1))), cmp(">=", e, lo)])
  let upper = g.pick([cmp("<", e, hi), cmp("<=", e, bin("-", hi, num(1))), cmp(">", hi, e), cmp("<", bin("+", e, num(1)), hi),
                      cmp("<", e, bin("-", hi, num(1))), cmp("<", e, hi)])
  if q < 0.55: conj(lower, upper)
  elif q < 0.65: conj(upper, lower)
  elif q < 0.75: negate(disj(cmp("<", e, lo), cmp(">=", e, hi)))
  elif q < 0.83: upper
  elif q < 0.90: lower
  else: conj(conj(lower, upper), g.compare)

proc cond(g: var Gen; d = 1): Expr =
  let q = g.roll
  if q < 0.5 or d <= 0: g.compare
  elif q < 0.7: conj(g.cond(d-1), g.cond(d-1))
  elif q < 0.82: disj(g.cond(d-1), g.cond(d-1))
  elif q < 0.9: negate(g.cond(d-1))
  else: g.guard(g.pick(g.lvals), g.pick(g.conts))

proc mutate(g: var Gen; c: Expr): Expr =
  ## Claim `c` perturbed, so true and false claims mix and the prover has to tell them apart.
  let q = g.roll
  case c.kind
  of eCmp:
    let (l, r) = (c.args[0], c.args[1])
    if q < 0.3: c
    elif q < 0.5:
      cmp({"<": "<=", "<=": "<", ">": ">=", ">=": ">", "==": "<=", "!=": "<"}.toTable[c.str], l, r)
    elif q < 0.7:
      let k = num(g.pick([1, 1, 2, -1]))
      cmp(c.str, bin("+", l, k), bin("+", r, k))
    elif q < 0.85: cmp(c.str, bin(g.pick(["+", "-"]), l, num(1)), r)
    else: cmp(c.str, l, bin(g.pick(["+", "-"]), r, num(1)))
  of eAnd, eOr:
    if q < 0.35: g.mutate(c.args[0])
    elif q < 0.7: g.mutate(c.args[1])
    else: Expr(kind: c.kind, args: @[g.mutate(c.args[0]), g.mutate(c.args[1])])
  of eNot: (if q < 0.6: c else: g.mutate(c.args[0]))
  else: c

proc claim(g: var Gen): Expr =
  ## A mutated guard in scope, a fact about a guarded index, an identity or a random condition.
  let q = g.roll
  if g.conds.len > 0 and q < 0.5: return g.mutate(g.pick(g.conds.last(4)))
  if g.guarded.len > 0 and q < 0.75:
    let (v, c) = g.pick(g.guarded.last(3))
    let hi = loHi(c)[1]
    let e = leaf(v)
    return g.pick([cmp("<", e, hi), cmp("<=", bin("+", e, num(1)), hi), cmp(">", hi, num(0)), cmp(">", bin("-", hi, e), num(0)),
      cmp(">=", bin("-", bin("-", hi, num(1)), e), num(0)), cmp(">=", e, num(0)), cmp("<", bin("+", e, num(1)), hi),
      cmp("<", bin("-", bin("-", hi, num(1)), e), hi), cmp(">=", hi, num(1)), cmp(">", bin("+", e, num(1)), e),
      cmp("<", bin("-", e, num(1)), e), cmp(">=", bin("*", e, num(2)), e), cmp("<=", bin("div", e, num(2)), e),
      cmp("<", bin("mod", e, num(8)), num(8))])
  if q < 0.85:
    let e = g.intExpr(1)
    if g.isA and g.chance(0.3):
      return g.pick([cmp(">=", call("abs", e), num(0)), cmp(">=", call("abs", e), e), cmp("<=", bin("and", call("abs", e), num(7)), num(7))])
    return g.pick([cmp(">", bin("+", e, num(1)), e), cmp(">=", bin("and", e, num(7)), num(0)), cmp("<=", bin("and", e, num(7)), num(7)),
      cmp(">=", leaf(g.pick(g.seqs) & ".len"), num(0)), cmp("<=", call("min", e, num(7)), num(7)), cmp(">=", call("max", e, num(0)), num(0)),
      cmp("<", bin("mod", e, num(8)), num(8)), cmp(">=", bin("mod", e, num(8)), num(0)), cmp("<=", bin("shr", e, num(1)), e),
      cmp(">=", bin("div", e, num(2)), num(0))])
  g.cond(1)

proc indexing(g: var Gen): Node =
  ## A read or store `c[ie]`: an `idx` claim, usually near a guard that bounds the index.
  var c: string
  var e: Expr
  if g.guarded.len > 0 and g.chance(0.7):
    let pr = g.pick(g.guarded.last(3))
    c = if g.chance(0.2): g.pick(g.conts) else: pr[1]
    e = leaf(pr[0])
  else:
    c = g.pick(g.conts)
    e = leaf(g.pick(g.lvals & g.lets))
  let hi = loHi(c)[1]
  let q = g.roll
  let ie =
    if q < 0.40: e
    elif q < 0.50: bin("+", e, num(1))
    elif q < 0.58: bin("-", e, num(1))
    elif q < 0.66: bin("-", bin("-", hi, num(1)), e)
    elif q < 0.72: bin("and", g.intExpr(1), num(g.pick([3, 7])))
    elif q < 0.77: bin("mod", e, if c in arrays: hi else: num(8))
    elif q < 0.82: call("clamp7", g.intExpr(1))
    elif q < 0.86: call("min", e, bin("-", hi, num(1)))
    elif q < 0.90: bin(g.pick(["div", "shr"]), e, num(g.pick([1, 2])))
    elif q < 0.94: bin("+", e, leaf(g.pick(g.lvals)))
    else: g.intExpr(2)
  if c == "st": g.newCheck("idx", @[ie], "result = result + ord(st[$1])", c)
  elif c in Writable and g.chance(0.3): g.newCheck("idx", @[ie, g.intExpr(1)], c & "[$1] = $2", c)
  else: g.newCheck("idx", @[ie], g.pick(g.writable & @["result", "result"]) & " = " & c & "[$1]", c)

proc barrier(g: var Gen): Node =
  ## A call or store that writes shared state (a func: only its var argument).
  let owned = without(["x", "y", "z", "i", "j"], g.frozen)
  var o = @["setGv($1)", "bumpGv()", "setTv($1)", "touchGo()", "clearGs()", "pokeP($1)", "poke(gb, $1)",
            "gfn($1)", "setCx($1)", "fn($1)", "q.f = $1", "n = $1", "gv = $1", "go.f = $1", "fadd(gs, $1)",
            "touchGo()", "setGv(1000000000)", "pokeP(-5)"]
  for i in countdown(o.high, 0):
    if (g.nogrow > 0 and "fadd" in o[i]) or
        (g.frozen.len > 0 and "pokeP" in o[i]):   # a clean loop's counter may be the stashed address
      o.delete(i)
  if owned.len > 0:
    let v = g.pick(owned)
    o.add ["mixG(" & v & ")", "fbump(" & v & ")", "fset(" & v & ", $1)", "fbump(" & v & ")"]
    if g.isA: o.add ["stash(addr " & v & ")", "stash(addr " & v & ")", "stash(addr " & v & ")"]
  if g.isA:
    let sh = among(g.writable, @Shared & @["o.f", "o.g"])
    if sh.len > 0:
      let v = g.pick(sh)
      o.add ["fbump(" & v & ")", "fset(" & v & ", $1)", "mixG(" & v & ")"]
  if "o.f" notin g.frozen and "o.g" notin g.frozen: o.add ["fclob(o)", "fclob(q)"]
  if g.nogrow == 0: o.add ["fadd(t, $1)", "fadd(o.items, $1)"]
  simple(g.pick(o), g.intExpr(1))

proc mutation(g: var Gen): Node =
  ## A write: to a local (often a guarded one), through a pointer, to a seq, or a barrier.
  let w = g.writable
  let q = g.roll
  if g.tryDepth > 0 and g.chance(0.35): return simple("risky($1)", g.intExpr(1))
  if g.chance(0.35): return g.barrier
  if w.len == 0: return simple("result = $1", g.intExpr(1))
  var target = g.pick(w)
  if g.guarded.len > 0 and g.chance(0.6):
    var cand: seq[string]
    for (v, _) in g.guarded.last(3):
      if v in w: cand.add v
    if cand.len > 0: target = g.pick(cand)
  if q < 0.22: return simple(target & " = $1", g.intExpr(2))
  if q < 0.36:
    return simple(g.pick(["inc ~", "dec ~", "inc(~, 2)", "dec(~, 2)", "~ += $1", "~ -= $1"]).replace("~", target), g.intExpr(1))
  if q < 0.40:
    var ps: seq[(string, string)]
    for pt in g.ptrs:
      if pt[1] notin g.frozen: ps.add pt
    return if ps.len > 0: simple(g.pick(ps)[0] & "[] = $1", g.intExpr(1)) else: simple(target & " = $1", g.intExpr(1))
  if q < 0.43 and g.isA: return simple("viaPtr(addr " & target & ", $1)", g.intExpr(1))
  if q < 0.54: return simple(g.pick(["inc ~", "dec ~", "~ = $1"]).replace("~", target), g.intExpr(1))
  if q < 0.62: return simple("bump(" & target & ")")
  if q < 0.68: return simple("setTo(" & target & ", $1)", g.intExpr(1))
  if q < 0.74 and w.len > 1: return simple("swap(" & target & ", " & g.pick(without(w, [target])) & ")")
  if q < 0.90:
    var c = g.pick(g.growable)
    if g.guarded.len > 0 and g.chance(0.6):
      var cand: seq[string]
      for (_, ct) in g.guarded.last(3):
        if ct in g.growable: cand.add ct
      if cand.len > 0: c = g.pick(cand)
    var o = @["~.setLen(" & $g.pick([0, 0, 1, 2, 3]) & ")", "shrink(~)", "dropOne(~)", "~ = @[]", "~ = s",
              "clobber(o)", "o = Obj()", "swap(t, o.items)", "discard ~.pop()"]
    if g.nogrow == 0: o.add ["~.add $1", "~.add $1", "~.setLen(" & $g.pick([5, 9]) & ")"]
    let s = g.pick(o).replace("~", c)
    if "pop" in s: return g.newCheck("pop", @[], s, c)
    if ("o.f" in g.frozen or "o.g" in g.frozen) and ("clobber" in s or "Obj()" in s):
      return simple("dropOne(" & c & ")")
    return simple(s, g.intExpr(1))
  if q < 0.95: return simple("w = " & g.pick(["w + 1'u8", "w - 1'u8", "uint8($1 and 255)", "w * 3'u8"]), g.intExpr(1))
  simple("result = $1", g.intExpr(2))

proc stmt(g: var Gen; depth: int): seq[Node]
proc stmts(g: var Gen; depth, n: int): seq[Node] =
  ## `n` statements; facts and names introduced here go out of scope at the end.
  let sv = (g.conds.len, g.guarded.len, g.lets.len, g.ptrs.len)
  for _ in 0 ..< n: result.add g.stmt(depth)
  g.conds.setLen sv[0]
  g.guarded.setLen sv[1]
  g.lets.setLen sv[2]
  g.ptrs.setLen sv[3]
proc body(g: var Gen; depth: int; facts: seq[Expr] = @[]; bound: seq[(string, string)] = @[]): seq[Node] =
  ## A nested block; `facts` and the `bound` (lvalue, container) pairs hold only inside it.
  let (a, b) = (g.conds.len, g.guarded.len)
  g.conds.add facts
  g.guarded.add bound
  result = g.stmts(depth - 1, g.rng.rand(1..4))
  g.conds.setLen a
  g.guarded.setLen b

proc stmt(g: var Gen; depth: int): seq[Node] =
  ## One statement (a loop comes with its init); at `depth` 0 only leaves.
  var q = g.roll(100)
  if depth <= 0 and q >= 62: q = g.roll(62)
  let noBreak = not g.isA and g.loops.len > 0 and g.loops[^1] == "for"   # for+break is finding 01
  # ---- leaves
  if q < 16: return @[g.indexing]
  if q < 28: return @[g.newCheck("assert", @[g.claim])]
  if q < 31:
    if g.chance(0.6): return @[g.newCheck("pos", @[g.intExpr(1)], g.pick(g.writable & @["result"]) & " = needsPos($1)")]
    return @[g.newCheck("between", @[g.intExpr(1), g.intExpr(0), g.intExpr(0)], "result = needsRange($1, $2, $3)")]
  if q < 36:
    let qq = g.roll
    if qq < 0.4: return @[g.newCheck("rng", @[g.intExpr(1)], g.pick(["r", "o.cnt"]) & " = $1")]
    if qq < 0.7:
      let step = g.pick([1, 1, -1, 2])
      let t = g.pick(["r", "r", "o.cnt"])
      let f = if step == 1: "inc " & t elif step == -1: "dec " & t else: "inc(" & t & ", 2)"
      return @[g.newCheck("rnginc", @[], f, t, step)]
    return @[g.newCheck("rng", @[g.intExpr(1)], "result = takesRT($1)")]
  if g.chance(0.10):   # a barrier, then restate a guard in scope (true before the barrier)
    result = @[g.barrier]
    if g.conds.len > 0: result.add g.newCheck("assert", @[g.pick(g.conds.last(4))])
    return
  if q < 38:
    let c = g.claim
    g.conds.add c
    return @[g.newCheck("assume", @[c])]
  if q < 52: return @[g.mutation]
  if q < 56:
    let nm = g.fresh("l")
    result = @[simple("let " & nm & " = $1", g.intExpr(2))]
    g.lets.add nm
    return
  if q < 58 and g.isA:
    let nm = g.fresh("p")
    let t = g.pick(g.lvals)
    g.ptrs.add (nm, t)
    return @[simple("let " & nm & " = addr " & t)]
  if q < 60:
    if g.loops.len > 0 and g.frozen.len == 0 and g.chance(0.7):
      return @[simple(if noBreak: "continue" else: g.pick(["break", "continue"]))]
    if g.loops.len > 0 and g.chance(0.5) and not noBreak: return @[simple("break")]
    return @[Node(kind: nIf, exprs: @[g.cond(1)], kids: @[simple("return")])]
  if q < 62: return @[simple("result = $1", g.intExpr(2))]
  # ---- compound
  if q < 74:   # guarded use
    let v = g.pick(g.lvals & g.lets)
    let c = g.pick(g.conts)
    let gd = g.guard(v, c)
    let kids = g.body(depth, @[gd], @[(v, c)])
    let e = g.chance(0.25)
    return @[Node(kind: nIf, exprs: @[gd], kids: kids, hasElse: e, els: if e: g.body(depth) else: @[])]
  if q < 79:   # random if
    let c = g.cond(2)
    let kids = g.body(depth, @[c])
    let e = g.chance(0.4)
    return @[Node(kind: nIf, exprs: @[c], kids: kids, hasElse: e, els: if e: g.body(depth, @[negate(c)]) else: @[])]
  if q < 84:   # guard clause
    let v = g.pick(g.lvals & g.lets)
    let c = g.pick(g.conts)
    let (lo, hi) = loHi(c)
    let e = leaf(v)
    let neg = g.pick([disj(cmp("<", e, lo), cmp(">=", e, hi)), cmp(">=", e, hi), cmp("<", e, lo), negate(g.guard(v, c))])
    g.conds.add(if neg.kind == eNot: neg.args[0] else: negate(neg))
    g.guarded.add (v, c)
    let ex = g.pick(["return", "return", if g.loops.len > 0 and not noBreak: "break" else: "return"])
    return @[Node(kind: nIf, exprs: @[neg], kids: @[simple(ex)])]
  if q < 91:   # counting while loop; a clean one writes neither its counter nor grows a seq
    let w = among(g.writable, ["i", "j", "x", "y", "z"])
    if w.len == 0: return @[g.mutation]
    let v = g.pick(w)
    let c = g.pick(g.conts)
    let (lo, hi) = loHi(c)
    let e = leaf(v)
    let down = g.chance(0.25)
    let clean = g.chance(0.5)
    var init, step: Node
    var test: Expr
    if down:
      init = simple(v & " = $1", bin("-", hi, num(1)))
      test = g.pick([cmp(">=", e, lo), cmp(">", e, bin("-", lo, num(1)))])
      step = simple(g.pick(["dec ~", "~ = ~ - 1", "dec ~"]).replace("~", v))
    else:
      init = simple(v & " = $1", g.pick([lo, lo, num(0), num(1), bin("and", g.intExpr(1), num(3))]))
      test = g.pick([cmp("<", e, hi), cmp("<", e, hi), cmp("<=", e, bin("-", hi, num(1))), cmp("<", bin("+", e, num(1)), hi),
                   cmp(if clean: "<" else: "!=", e, hi)])
      step = simple(g.pick(["inc ~", "inc ~", "~ = ~ + 1", "inc(~, 2)", "~ += 1"]).replace("~", v))
    if c != "st" and g.chance(0.25):
      test = conj(test, Expr(kind: eChk, id: g.newId, str: c, rhs: g.pick(["!=", "==", ">", "<"]) & " " & $g.pick([0, 3, 5]),
                     args: @[e]))
    elif g.chance(0.15): test = conj(test, g.compare)
    g.loops.add "while"
    if clean:
      g.frozen.add v
      inc g.nogrow
    var kids = g.body(depth, @[test], @[(v, c)])
    if clean:
      discard g.frozen.pop
      dec g.nogrow
    discard g.loops.pop
    if clean or g.chance(0.9): kids.add step
    return @[init, Node(kind: nWhile, exprs: @[test], kids: kids, fuel: if clean: "" else: g.pick(["break", "break", "return"]))]
  if q < 97:   # for loop
    let kv = g.fresh("k")
    let c = g.pick(g.conts)
    let (lo, hi) = loHi(c)
    let qq = g.roll
    var fmt: string
    var ex: seq[Expr]
    if qq < 0.45:
      fmt = "for " & kv & " in $1 ..< $2:"
      ex = @[g.pick([lo, lo, num(0), num(1)]), g.pick([hi, hi, g.small])]
    elif qq < 0.75:
      fmt = "for " & kv & " in $1 .. $2:"
      ex = @[g.pick([lo, num(0), num(1)]), g.pick([bin("-", hi, num(1)), bin("-", hi, num(1)), g.small])]
    else:
      fmt = "for " & kv & " in countdown($1, $2):"
      ex = @[g.pick([bin("-", hi, num(1)), g.small]), g.pick([lo, num(0), num(1)])]
    g.lets.add kv
    g.loops.add "for"
    let kids = g.body(depth, @[], @[(kv, c)])
    discard g.loops.pop
    g.lets.delete(g.lets.find(kv))
    return @[Node(kind: nFor, fmt: fmt, exprs: ex, kids: kids)]
  if q < 98.5:   # try/except around risky(); flavour C: the try body writes nothing (finding 08)
    inc g.tryDepth
    let n0 = g.frozen.len
    if not g.isA:
      g.frozen.add g.lvals
      inc g.nogrow
    var kids = g.body(depth)
    if not g.isA:
      g.frozen.setLen n0
      dec g.nogrow
    dec g.tryDepth
    kids.insert(simple("risky($1)", g.intExpr(1)), g.rng.rand(kids.len))
    return @[Node(kind: nTry, kids: kids, hasElse: true, els: g.body(depth))]
  # case with ranges
  let v = g.pick(g.lvals)
  let e = leaf(v)
  var cuts: seq[int]
  for k in -1 .. 9: cuts.add k
  g.rng.shuffle(cuts)
  cuts = cuts[0 ..< g.rng.rand(2..4)].sorted
  var brs: seq[Node]
  for bi in 0 ..< cuts.len - 1:
    let lo = cuts[bi]
    var hi = cuts[bi + 1] - 1
    var lab: string
    if hi > lo and g.chance(0.8): lab = num(lo).str & ".." & $hi
    elif hi == lo + 1: lab = num(lo).str & ", " & $hi
    else:
      hi = lo
      lab = num(lo).str
    brs.add Node(kind: nOf, fmt: lab, kids: g.body(depth, @[conj(cmp(">=", e, num(lo)), cmp("<=", e, num(hi)))],
                                              @[(v, g.pick(["ar", "la", "o.arr"]))]))
  @[Node(kind: nCase, exprs: @[e], kids: brs, els:if g.chance(0.5): g.body(depth) else: @[])]

proc genProc(seed, idx: int; flavour: char; ids: var int): Node =
  ## Proc `p<idx>`; `ids` is the module's next claim id.
  var g = Gen(rng: initRand(seed), isA: flavour == 'A', ids: ids, lvals: @["x", "y", "z", "i", "j", "o.f", "o.g"],
              seqs: @["s", "t", "o.items"], growable: @["t", "o.items"],
              conts: @["ar", "ar", "la", "o.arr", "s", "s", "t", "t", "o.items", "st"])
  if g.isA:
    g.lvals.add Shared
    for x in [addr g.seqs, addr g.growable, addr g.conts]: x[].add ["gs", "q.items"]
  result = Node(kind: nProc, id: idx, flavour: flavour, ensId: -1, kids: g.stmts(3, g.rng.rand(3..7)))
  if g.chance(0.3):
    let res = leaf("result")
    if g.chance(0.5):   # make the claim plausible: set result from a bounded expression last
      result.kids.add simple("result = $1", g.pick([call("clamp7", g.intExpr(1)), bin("and", g.intExpr(1), num(7)),
        call("nonNeg", g.intExpr(1)), leaf("s.len"), call("min", leaf("a"), leaf("b")), bin("+", leaf("a"), num(1)),
        bin("mod", g.intExpr(1), num(8)), bin("div", leaf("a"), num(2))]))
    result.ensures = g.pick([cmp(">=", res, num(0)), cmp("<=", res, num(7)), conj(cmp(">=", res, num(0)), cmp("<=", res, num(7))),
      cmp("<=", res, leaf("a")), cmp("<", res, leaf("s.len")), cmp("<=", res, leaf("s.len")), cmp(">", res, leaf("a")),
      cmp("<", res, num(8)), cmp(">=", res, num(-7)), cmp("<=", res, leaf("b")), disj(cmp(">=", res, num(0)), cmp("<", leaf("a"), num(0)))])
    result.ensId = g.newId
  ids = g.ids

# ---- func rule (4ba90a78) ------------------------------------------------------

const
  FuncPre = """
type
  Plain = object
    x: int
    arr: array[3, int]
    s: seq[int]
  NodeObj = object
    x: int
    s: seq[int]
    pl: Plain
  Node = ref NodeObj
  Tup = tuple[a: int, r: Node]
  Holder = object
    x: int
    r: Node
    p: ptr Plain
    pl: Plain
    s: seq[int]
    rs: seq[Node]
    ps: seq[Plain]
    arr: array[3, int]
    ra: array[2, Node]
    t: Tup
    ua: ptr UncheckedArray[int]
func fb(x: var int) = inc x
func fsq(x: var seq[int]) = x.add 1
template tw(x: untyped) = x = 7
"""
  FuncMsg = "through a ref/ptr in a `.noSideEffect` context"
  # (param decl, prologue, head expr, type, head is mutable)
  Heads = [("h: var Holder", "", "h", "Holder", true), ("h: var Holder", "", "h", "Holder", true),
    ("h: var Holder", "", "h", "Holder", true), ("h: Holder", "var c = h", "c", "Holder", true),
    ("h: Holder", "", "h", "Holder", false), ("n: var Node", "", "n", "Node", true), ("n: Node", "", "n", "Node", false),
    ("p: ptr Plain", "", "p", "PPlain", false), ("p: var ptr Plain", "", "p", "PPlain", true),
    ("s: var seq[Node]", "", "s", "SeqNode", true), ("s: var seq[Plain]", "", "s", "SeqPlain", true),
    ("a: var array[2, Node]", "", "a", "ArrNode", true), ("o: var openArray[int]", "", "o", "OAInt", true),
    ("pl: var Plain", "", "pl", "Plain", true), ("t: var Tup", "", "t", "Tup", true)]
# Types of FuncPre for accessPath: "obj" then name:type fields, or a container and its element type.
let funcTypes = {"Holder": "obj x:int r:Node p:PPlain pl:Plain s:SeqInt rs:SeqNode ps:SeqPlain arr:ArrInt ra:ArrNode t:Tup ua:UA",
  "Plain": "obj x:int arr:ArrInt s:SeqInt", "NodeObj": "obj x:int s:SeqInt pl:Plain", "Tup": "obj a:int r:Node",
  "Node": "ref NodeObj", "PPlain": "ptr Plain", "SeqInt": "seq int", "SeqNode": "seq Node", "SeqPlain": "seq Plain",
  "ArrInt": "arr int", "ArrNode": "arr Node", "OAInt": "arr int", "UA": "ua int", "int": "int"}.toTable

proc accessPath(r: var Rand; ty0, path0: string; steps: int): (string, string, bool, string) =
  ## A random access path: (path, its type, behind a ref/ptr, shape). Shape letters: f field,
  ## R field through ref/ptr, D `[]`, E element, U UncheckedArray.
  var (ty, path, behind, shape) = (ty0, path0, false, "")
  for _ in 0 ..< steps:
    let w = funcTypes[ty].split(' ')
    var field = ""   # "name:type"
    case w[0]
    of "int": break
    of "obj":
      field = r.sample(w[1 .. ^1])
      shape.add 'f'
    of "ref", "ptr":
      behind = true
      if r.rand(1.0) < 0.3:
        path.add "[]"
        ty = w[1]
        shape.add 'D'
      else:
        field = r.sample(funcTypes[w[1]].split(' ')[1 .. ^1])
        shape.add 'R'
    else:
      path.add "[0]"
      ty = w[1]
      behind = behind or w[0] == "ua"
      shape.add(if w[0] == "ua": 'U' else: 'E')
    if field != "":
      let c = field.find(':')
      path.add "." & field.substr(0, c - 1)
      ty = field.substr(c + 1)
    if r.rand(1.0) < 0.25: break
  (path, ty, behind, shape)

proc head(s: string; stop: set[char]): string =
  ## `s` up to the first character in `stop`.
  let k = s.find(stop)
  if k < 0: s else: s.substr(0, k - 1)

proc writes(ty, p: string): seq[string] =
  ## Statements that write location `p` of type `ty`.
  case ty
  of "int": @[p & " = 5", "inc " & p, p & " += 2", "fb(" & p & ")", "tw(" & p & ")", "swap(" & p & ", loc)",
              "let q = addr " & p & "; q[] = 3"]
  of "SeqInt": @[p & ".add 1", p & ".setLen 0", "fsq(" & p & ")", p & " = @[]"]
  of "Plain", "NodeObj": @[p & " = default(" & ty & ")"]
  of "Node": @[p & " = Node(x: 1)"]
  of "SeqNode": @[p & ".add Node(x: 1)"]   # no setLen: Node is not nil, it has no default
  of "SeqPlain": @[p & ".setLen 0", p & ".add default(Plain)"]
  of "ArrInt": @[p & "[1] = 4"]
  else: @[]

type FuncCase = tuple[text: string, legal: bool, why, form: string]  ## why, form: for the signature
proc funcCase(r: var Rand; i: int): FuncCase =
  ## One routine whose legality follows from the func rule alone: in a noSideEffect routine (func,
  ## `.noSideEffect` proc, iterator) a write is illegal iff its path dereferences a ref/ptr. A
  ## `.sideEffect` func, a proc and a `cast(noSideEffect)` block may write anywhere.
  for _ in 0 ..< 50:
    let (decl, pro, head, ty, mut) = r.sample(Heads)
    let (path, pty, behind, sh) = accessPath(r, ty, head, r.rand(4))
    let shape = if sh == "": "-" else: sh
    let kind = r.sample(["func", "func", "func", "nse", "iter", "proc", "fse", "castfunc", "varres", "varres"])
    if not mut and not behind: continue   # immutable for another reason: not this rule
    if kind == "varres":   # returning a location as `var T` counts as writing it
      if pty != "int" or ": var " notin decl or pro != "": continue
      let rk = r.sample(["func", "nse", "proc"])
      let form = r.sample(["expr", "return", "result"])
      let hdr = (if rk == "func": "func c" else: "proc c") & $i & "(" & decl & "): var int" &
                (if rk == "nse": " {.noSideEffect.}" else: "") & " ="
      let text = if form == "expr": hdr & " " & path & "\n"
                 else: hdr & "\n  " & (if form == "return": "return " else: "result = ") & path & "\n"
      return (text, not behind or rk == "proc", "var-result " & rk & " behind=" & $behind & " " & form,
              "varres-" & form & " path=" & shape)
    let ws = writes(pty, path)
    if ws.len == 0: continue
    let w = r.sample(ws)
    if ty == "OAInt" and (w.endsWith(".add 1") or "setLen" in w or "= @[]" in w or "fsq" in w): continue
    let deref = behind or w.startsWith("let q = addr")   # q[] is a dereference
    var pre = if pro != "": @[pro] else: @[]
    if "loc" in w: pre.add "var loc = 0"
    var s = w.replace("; ", "\n  ")
    if kind == "castfunc": s = "{.cast(noSideEffect).}:\n    " & w.replace("; ", "\n    ")
    if kind == "func" and r.rand(1.0) < 0.2: s = "if true:\n    " & w.replace("; ", "\n    ")
    let hd = case kind
      of "func", "castfunc": "func c$1($2) ="
      of "nse": "proc c$1($2) {.noSideEffect.} ="
      of "proc": "proc c$1($2) ="
      of "fse": "func c$1($2) {.sideEffect.} ="
      else: "iterator c$1($2): int ="
    let text = (hd % [$i, decl]) & "\n  " & (pre & @[s]).join("\n  ") & "\n" & (if kind == "iter": "  yield 1\n" else: "")
    var op = head(w, {'(', ' '})
    if w.startsWith(path):   # the operator after the path
      for t in w.substr(path.len).splitWhitespace:
        op = t
        break
    return (text, not deref or kind notin ["func", "nse", "iter"], kind & " behind=" & $deref & " head=" & decl,
            op & " path=" & shape)

proc renderFuncs(cs: seq[FuncCase]): (string, seq[(int, int)]) =
  ## The module and each routine's line range, to attribute errors.
  var ls = FuncPre.strip(leading = false).splitLines
  for c in cs:
    let lo = ls.len + 1
    ls.add c.text.strip(leading = false).splitLines
    result[1].add (lo, ls.len)
  result[0] = ls.join("\n") & "\n"

# ---- running ---------------------------------------------------------------------

type
  Err = tuple[ln: int, msg: string]
  Run = tuple[status: string, reached, passed, failed: seq[int], witness: Table[int, string], output: string]

proc build(src, name, cmd: string): (int, string) =
  ## Runs `nimony <cmd>` on `src` saved as <workDir>/<name>.nim; returns (exit code, output).
  writeFile(workDir / name & ".nim", src)
  let c = "cd " & quoteShell(workDir) & " && timeout -k 5 180 " & quoteShell(nimony) & " " & cmd &
          " --nimcache:nc_" & name & " " & name & ".nim"
  for _ in 0 .. 1:
    let (o, rc) = execCmdEx(c)
    result = (rc, o)
    if rc == 0 or "deps.nif" notin o: break   # known flake (report 08): retry once

proc errors(o, name: string): seq[Err] =
  ## `file(line, col) Error: msg`; an error in another file gets line 0.
  let file = name & ".nim"
  for l in o.splitLines:
    let k = l.find(") Error: ")
    if k < 0: continue
    let b = l.rfind('(', last = k)
    if b < 0: continue
    let pos = l.substr(b + 1, k - 1)
    let comma = pos.find(", ")
    if comma < 0: continue
    let (ln, col) = (pos.substr(0, comma - 1), pos.substr(comma + 2))
    if ln.len == 0 or col.len == 0 or not (ln & col).allCharsInSet(Digits): continue
    var m = l.substr(k + 9)
    let v = m.find(" [pass --verbose")
    if v >= 0: m.setLen v
    let here = l.substr(0, b - 1).extractFilename == file  # not `strings.nim`
    result.add ((if here: parseInt(ln) else: 0), m)

proc fromProver(m: string): bool =
  for w in ["cannot prove", "violated", "value out of range", "unexpectedly"]:
    if w in m: return true
proc crashy(o: string): bool =
  ## The compiler failed internally, not with an ordinary error.
  for l in o.splitLines:
    if ") Error: " in l or "nifmake: command failed" in l or l.startsWith("FAILURE"): continue
    let t = l.toLowerAscii
    for w in ["assertiondefect", "traceback", "sigsegv", "illegal storage", " bug", "unreachable", "indexdefect",
              "out of bounds", "signal", "[assert"]:
      if w in t: return true

proc runOracle(src, name: string): Run =
  ## Compile in mode O and run; the program prints R/P/F <id> (reached/passed/failed) and W <id> <input>.
  let (rc, o) = build(src, name, "c")
  result.output = o
  result.status = if rc in [124, 137]: "timeout" else: "fail"
  if rc != 0: return
  var exe = ""
  for f in walkDirRec(workDir / "nc_" & name):
    if f.extractFilename == name: exe = f
  let (o2, rc2) = execCmdEx("timeout -k 2 60 " & quoteShell(exe))
  result.output = o2
  if rc2 in [124, 137]: result.status = "timeout"
  for l in o2.splitLines:
    if l == "END" and rc2 == 0: result.status = "ok"
    elif l.len > 2 and l[0] in "RPFW" and l[1] == ' ':
      let sp = l.find(' ', 2)   # W <id> <input>
      let id = parseInt(l.substr(2, (if sp < 0: l.len else: sp) - 1))
      case l[0]
      of 'R': result.reached.add id
      of 'P': result.passed.add id
      of 'F': result.failed.add id
      else: result.witness[id] = l.substr(sp + 1)

proc report(kind: string; s, id: int; sig, src, txt: string): string =
  result = outDir / kind & "_" & $s & "_" & $id
  writeFile(result & ".nim", src)
  if txt != "": writeFile(result & ".txt", txt & "\n")
  let f = outDir / "log.csv"
  let hdr = not fileExists(f)
  let h = open(f, fmAppend)
  if hdr: h.write "time_s,programs,finding_id,signature\n"
  h.write formatFloat(epochTime() - start, ffDecimal, 1) & "," & $programs & "," & result.extractFilename & "," &
          sig.replace(",", ";") & "\n"
  h.close
  echo "  ", kind, ": ", sig

# ---- oracle ------------------------------------------------------------------------

proc settle(ps: var seq[Node]; nclaims: int; rejected: var Table[int, (int, string)]): (string, string, string) =
  ## Deletes every claim the prover rejects and recompiles until the module is accepted, so what is
  ## left is exactly what it proved. rejected[id] = (round, message); returns (status, source, output).
  for rnd in 0 ..< 10:
    let (src, lines) = render(ps, false, nclaims)
    let (rc, o) = build(src, "s", "c")
    if rc == 0: return ("ok", src, o)
    if rc in [124, 137]: return ("timeout", src, o)
    let es = errors(o, "s")
    if es.len == 0 or crashy(o): return ("crash", src, o)
    var progress = false
    var drop: seq[Node]
    for e in es:
      if e.ln < 1 or e.ln > lines.len or lines[e.ln - 1].owner == nil: continue
      let (p, n) = (lines[e.ln - 1].owner, lines[e.ln - 1].node)
      if fromProver(e.msg) and "postcondition" in e.msg:   # reported at a `return`: drop the proc's ensures
        if p.ensures != nil:
          discard rejected.hasKeyOrPut(p.ensId, (rnd, e.msg))
          p.ensures = nil
          progress = true
      elif not fromProver(e.msg) or n == nil:   # not about a claim: the generator's fault, drop the proc
        if p notin drop: drop.add p
      elif n.kind == nChk and n.check != "assume":
        discard rejected.hasKeyOrPut(n.id, (rnd, e.msg))
        if subst(p, n): progress = true
      elif n.kind in {nIf, nWhile} and condIds(n.exprs[0]).len > 0:   # keep the statement, lose the guard's index
        for c in condIds(n.exprs[0]): discard rejected.hasKeyOrPut(c, (rnd, e.msg))
        n.exprs[0] = unchecked(n.exprs[0])
        progress = true
      elif n.kind in {nS, nChk} and subst(p, n): progress = true
      elif p notin drop: drop.add p
    for p in drop: ps.delete(ps.find(p))
    if not progress and drop.len == 0: return ("stuck", src, o)
  ("rounds", "", "")

proc hasWord(s, w: string): bool =
  ## `w` occurs in `s` as a whole identifier.
  var i = s.find(w)
  while i >= 0:
    if (i == 0 or s[i-1] notin IdentChars) and (i + w.len >= s.len or s[i + w.len] notin IdentChars): return true
    i = s.find(w, i + 1)

proc classify(p: Node; cid, nclaims: int): string =
  ## Signature tags: the shared variables the failing claim names and the known-bug constructs in the proc.
  let (src, lines) = render(@[p], false, nclaims)
  var texts: seq[string]
  for l in lines:
    if l.node != nil and hasClaim(l.node, cid): texts.add l.text
  let claim = if p.ensId == cid: "result" else: texts.join(" ")
  var tags: seq[string]
  for v in ["gv", "tv", "go", "gs", "n", "q", "cx", "o", "t"]:
    if hasWord(claim, v): tags.add "claim-" & v
  var inFor, forBreak, negShr, hasAbs, address, stash, isTry: bool
  for raw in src.substr(src.find("proc p" & $p.id & "(")).splitLines:
    let l = raw.strip
    if l.startsWith("for "): inFor = true
    if inFor and hasWord(l, "break"): forBreak = true
    if "(-1) shr" in l or "(-2) shr" in l: negShr = true
    if "abs(" in l: hasAbs = true
    if (l.startsWith("let p") and " = addr " in l) or "viaPtr(addr" in l: address = true
    if "stash(" in l: stash = true
    if l == "try:": isTry = true
  for (on, tag) in [(forBreak, "forbreak"), (negShr, "negshr"), (hasAbs, "abs"), (address, "addr"), (stash, "stash"),
                    (isTry, "try")]:
    if on: tags.add tag
  if tags.len == 0: "none" else: tags.join("+")

proc persists(kind: string; cid, nclaims: int): proc (p: Node): bool =
  ## Does the finding persist for the single proc `p`?
  result = proc (p: Node): bool =
    let (src, lines) = render(@[p], false, nclaims)
    let (rc, o) = build(src, "ms", "c")
    if kind == "unsound":
      if rc != 0: return false
    else:   # false-violation: the same rejection and nothing else, and the claim passes at run time
      let es = errors(o, "ms")
      var same = false
      for e in es:
        if not fromProver(e.msg): return false
        if p.ensId == cid: same = same or (p.ensures != nil and "postcondition violated" in e.msg)
        elif e.ln in 1 .. lines.len and lines[e.ln - 1].node != nil and hasClaim(lines[e.ln - 1].node, cid) and
            ("violated" in e.msg or "out of range" in e.msg): same = true
      if not same: return false
    let r = runOracle(render(@[p], true, nclaims)[0], "mo")
    r.status == "ok" and cid in (if kind == "unsound": r.failed else: r.passed)

# ---- reduction ----------------------------------------------------------------------

proc smaller(e: Expr): seq[Expr] =
  ## Smaller expressions of the same type for `e` or any sub-expression.
  if e.kind in {eCmp, eAnd, eOr, eNot, eChk, eTrue, eFalse}:
    if e.kind in {eAnd, eOr, eNot}: result.add e.args
    if e.kind notin {eTrue, eCmp}: result.add Expr(kind: eTrue)
  else:
    if e.kind in {eBin, eCall}: result.add e.args
    if e.kind != eLeaf: result.add num(0)
  for i in 0 ..< e.args.len:
    for x in smaller(e.args[i]):
      let y = Expr(kind: e.kind, str: e.str, rhs: e.rhs, id: e.id, args: e.args)
      y.args[i] = x
      result.add y

proc unwrap(q: Node; i, v: int): bool =
  ## Variant v of simplifying node i: replace it by its v-th body (0..2), or drop else/fuel (3), ensures (proc).
  let ns = walk(q)
  if i >= ns.len: return false
  let n = ns[i]
  if n.kind == nProc:
    result = v == 0 and n.ensures != nil
    if result: n.ensures = nil
  elif v == 3:
    if n.kind == nIf and n.hasElse:
      n.hasElse = false
      n.els = @[]
      return true
    if n.kind == nWhile and n.fuel != "":
      n.fuel = ""
      return true
  else:
    let ls = case n.kind
      of nCase:
        var bs: seq[seq[Node]]
        for b in n.kids: bs.add b.kids
        bs & @[n.els]
      of nIf, nTry: (if n.hasElse: @[n.kids, n.els] else: @[n.kids])
      of nWhile, nFor: @[n.kids]
      else: @[]
    if v < ls.len: return subst(q, n, ls[v])

proc reduce(p0: Node; still: proc (p: Node): bool): Node =
  ## Delta debugging: keeps every deletion, unwrapping and smaller expression after which `still`
  ## holds, until nothing changes or `budget` tests are spent.
  var p = p0
  var tests = 0
  proc attempt(edit: proc (q: Node): bool): bool =
    if tests >= budget: return false
    let q = clone(p)
    if not edit(q): return false
    inc tests
    result = still(q)
    if result: p = q
  var changed = true
  while changed and tests < budget:
    changed = false
    var i = 1
    while i < walk(p).len:   # delete statements (parents first: a whole subtree in one test)
      if attempt(proc (q: Node): bool =
          let ns = walk(q)
          i < ns.len and ns[i].kind != nOf and subst(q, ns[i])): changed = true
      else: inc i
    i = walk(p).len - 1
    while i >= 0:   # unwrap compound statements, drop else/fuel/ensures
      for v in 0 .. 3:
        if attempt(proc (q: Node): bool = unwrap(q, i, v)):
          changed = true
          break
      i = min(i, walk(p).len) - 1
    i = walk(p).len - 1
    while i >= 0:   # simplify expressions
      for ei in 0 ..< walk(p)[i].exprs.len:
        var again = true
        while again and tests < budget:
          again = false
          for c in smaller(walk(p)[i].exprs[ei]):
            let cc = c
            if attempt(proc (q: Node): bool =
                walk(q)[i].exprs[ei] = cc
                true):
              changed = true
              again = true
              break
      dec i
  p

proc minimize(base: string; p: Node; still: proc (p: Node): bool; nclaims: int) =
  ## Reduces the finding's proc to <base>.reduced.nim.
  if not doReduce: return
  if not still(p):
    echo "  not reproduced standalone"
    return
  let q = reduce(p, still)
  writeFile(base & ".reduced.nim", render(@[q], false, nclaims)[0])
  echo "  reduced ", walk(p).len, " -> ", walk(q).len, " nodes: ", base, ".reduced.nim"

# ---- batches ----------------------------------------------------------------------

proc soundBatch(seed: int): int =
  ## A staticContracts module of 16 procs through settle and the oracle; returns the number of findings.
  let flavour = if seed mod 3 == 0: 'A' else: 'C'
  var ids = 0
  var procs: seq[Node]
  for i in 0 ..< 16: procs.add genProc(seed * 1000 + i + 1, i, flavour, ids)
  programs += 16
  let nclaims = ids
  var orig: seq[Node]
  for p in procs: orig.add clone(p)
  var kinds = initTable[int, string]()
  for p in orig:
    for (id, k) in claims(p): kinds[id] = k
  var rejected = initTable[int, (int, string)]()
  let (status, src, o) = settle(procs, nclaims, rejected)
  if status != "ok":
    discard report(if status == "crash": "crash" else: "odd", seed, 0,
                   (if status == "crash": "crash" else: "odd:settle-" & status), src, o)
    return 1
  var owner = initTable[int, Node]()
  for p in procs:
    for (id, _) in claims(p): owner[id] = p
  # what is left was proved: as run-time tests, a claim that fails is unsound
  let run = runOracle(render(procs, true, nclaims)[0], "o")
  echo "seed ", seed, " ", flavour, ": ", procs.len, " procs, ", kinds.len, " checks, ", rejected.len, " rejected, ", owner.len,
       " proved, oracle ", run.status
  if run.status != "ok":
    discard report("odd", seed, 0, "odd:oracle-" & run.status, render(procs, true, nclaims)[0], run.output)
    return 1
  for cid in run.failed.sorted:
    if cid notin owner: continue
    let p = owner[cid]
    let base = report("unsound", seed, cid, "unsound/" & flavour & ":" & kinds[cid] & ":" & classify(p, cid, nclaims),
                      render(@[p], false, nclaims)[0], run.witness.getOrDefault(cid))
    inc result
    minimize(base, p, persists("unsound", cid, nclaims), nclaims)
  if rejected.len == 0: return
  # the reverse direction, on the original module: claims rejected in round 0 (before any deletion)
  let back = runOracle(render(orig, true, nclaims)[0], "o2")
  if back.status != "ok": return
  var origOwner = initTable[int, Node]()
  for p in orig:
    for (id, _) in claims(p): origOwner[id] = p
  var rejIds: seq[int]
  for cid in rejected.keys: rejIds.add cid
  for cid in rejIds.sorted:
    let (rnd, msg) = rejected[cid]
    if rnd != 0 or cid notin origOwner: continue
    if "cannot prove" in msg:
      if cid in back.reached and cid notin back.failed:
        let h = open(outDir / "incomplete.log", fmAppend)
        h.write $seed & "\t" & kinds[cid] & "\t" & msg & "\n"
        h.close
    elif cid in back.passed and kinds[cid] != "ensures":   # an ensures is judged per `return`, the oracle sees the proc
      let base = report("false-violation", seed, cid, "false-violation:" & kinds[cid] & ":" & head(msg, {':'}),
                        render(@[origOwner[cid]], false, nclaims)[0], msg)
      inc result
      minimize(base, origOwner[cid], persists("false-violation", cid, nclaims), nclaims)

proc msgsIn(es: seq[Err]; span: (int, int); elsewhere = false): seq[string] =
  ## Messages of the errors in lines `span`, and with `elsewhere` those in other files.
  for e in es:
    if (elsewhere and e.ln == 0) or e.ln in span[0] .. span[1]: result.add e.msg

proc blankPaths(m: string): string =
  ## `m` with every access path (a quoted word with `.` or `[`) replaced by PATH, for the signature.
  var ws: seq[string]
  for it in m.split(' '):
    let w = it.strip(chars = {'`', '\''})
    ws.add(if w.len > 0 and w[0] in {'a'..'z'} and ('.' in w or '[' in w): "PATH" else: it)
  ws.join(" ")

proc funcBatch(seed: int): int =
  ## A module of func-rule routines judged by `nimony check`; returns the number of findings.
  var r = initRand(seed)
  var cases: seq[FuncCase]
  for i in 0 ..< 40:
    let c = funcCase(r, i)
    if c.text != "": cases.add c
  programs += cases.len
  let (src, ranges) = renderFuncs(cases)
  let (rc, o) = build(src, "f", "check")
  let es = errors(o, "f")
  if rc in [124, 137] or (rc != 0 and es.len == 0):
    discard report("func-crash", seed, 0, "func-crash:" & $rc, src, o)
    return 1
  var msgs = initTable[int, seq[string]]()
  var mixed = false
  for e in es:
    if e.ln == 0 or FuncMsg notin e.msg: mixed = true
  if mixed:
    # another error can stop the pass that checks the rule: judge each routine on its own
    for i, c in cases:
      let (t1, r1) = renderFuncs(@[c])
      let (rc1, o1) = build(t1, "f1", "check")
      let e1 = errors(o1, "f1")
      if rc1 in [124, 137] or (rc1 != 0 and e1.len == 0):
        discard report("func-crash", seed, i, "func-crash:" & $rc1, t1, o1)
        inc result
      else: msgs[i] = msgsIn(e1, r1[0], elsewhere = true)
  else:
    for i in 0 ..< cases.len: msgs[i] = msgsIn(es, ranges[i])
  for i, c in cases:
    if i notin msgs: continue
    let ms = msgs[i]
    var rule, other: seq[string]
    for m in ms:
      if FuncMsg in m: rule.add m else: other.add m
    let kind = if not c.legal and ms.len == 0: "func-accepts-invalid"
               elif c.legal and ms.len > 0: "func-rejects-valid"
               elif not c.legal and other.len > 0 and rule.len == 0: "func-other-error"
               else: ""
    if kind == "": continue
    var sig = kind & ":" & c.why & " " & c.form
    if ms.len > 0:   # the message with its access paths blanked
      sig.add ":" & blankPaths(if other.len > 0: other[0] else: rule[0])
    discard report(kind, seed, i, sig, renderFuncs(@[c])[0], ms.join("\n"))
    inc result
  echo "seed ", seed, " F: ", cases.len, " routines, ", result, " findings"

proc main() =
  var seed = int(epochTime() * 1000) mod 1_000_000
  var count = 10
  var minutes = 0.0
  outDir = getAppDir() / "out"
  var work = getAppDir() / "work"
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "minutes": minutes = parseFloat(val)
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": work = val
    of "budget": budget = parseInt(val)
    of "noreduce": doReduce = false
    else: quit "unknown option: " & key
  if minutes > 0 and count == 10: count = high(int)
  nimony = absolutePath(nimony)
  outDir = absolutePath(outDir)
  workDir = absolutePath(work) / ("w" & $seed)
  createDir(outDir)
  createDir(workDir)
  var found = 0
  var k = 0
  while k < count and (minutes == 0 or epochTime() - start < minutes * 60):
    let s = seed + k
    found += (if s mod 3 == 2: funcBatch(s) else: soundBatch(s))
    inc k
  var ru: Rusage
  discard getrusage(RUSAGE_CHILDREN, addr ru)
  let cpu = cpuTime() + float(ru.ru_utime.tv_sec) + float(ru.ru_stime.tv_sec)
  echo k, " modules, ", programs, " programs, ", found, " findings, wall ", int(epochTime() - start), " s, cpu ", int(cpu),
       " s - ", outDir

main()
