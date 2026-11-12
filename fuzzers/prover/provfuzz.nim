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

import std / [os, osproc, strutils, random, times, parseopt, tables, sequtils, algorithm, posix]

type
  EK = enum eLeaf, eBin, eCmp, eAnd, eOr, eNot, eCall, eChk, eTrue, eFalse
  E = ref object
    k: EK
    s, t: string                 ## leaf text / operator / callee; eChk: s = container, t = "op rhs"
    a: seq[E]
    id: int
  NK = enum nProc, nS, nChk, nIf, nWhile, nFor, nTry, nCase, nOf
  Node = ref object
    k: NK
    fmt, ck, cont, fuel: string  ## fmt: the statement, with $1.. for `ex`
    ex: seq[E]
    kids, els: seq[Node]         ## nCase: kids are the nOf branches
    hasEls: bool
    id, step, ensid: int         ## nProc: id = proc index
    ens: E                       ## nProc: `.ensures`, nil = none
    fl: char
  Ln = tuple[s: string, p, n: Node]   ## rendered line, its proc and its node

var
  nimony = "/home/ageralis/Projects/nimony/bin/nimony"
  wd, outDir: string
  budget = 150
  doReduce = true
  np = 0                         ## programs (procs, routines) generated so far
  t0 = epochTime()

# ---- expressions -------------------------------------------------------------

proc L(s: string): E = E(k: eLeaf, s: s)
proc N(k: int): E = L(if k < 0: "(" & $k & ")" else: $k)
proc B(op: string; l, r: E): E = E(k: eBin, s: op, a: @[l, r])
proc C(op: string; l, r: E): E = E(k: eCmp, s: op, a: @[l, r])
proc And(l, r: E): E = E(k: eAnd, a: @[l, r])
proc Or(l, r: E): E = E(k: eOr, a: @[l, r])
proc Not(x: E): E = E(k: eNot, a: @[x])
proc F(f: string; xs: varargs[E]): E = E(k: eCall, s: f, a: @xs)
proc isBool(e: E): bool = e.k in {eCmp, eAnd, eOr, eNot, eChk, eTrue, eFalse}

let arrs = {"ar": (0, 7), "la": (2, 5), "o.arr": (0, 3)}.toTable
proc loHi(c: string): (E, E) =
  if c in arrs: (N(arrs[c][0]), N(arrs[c][1] + 1)) else: (N(0), L(c & ".len"))
proc bounds(c: string; e: E): E =
  let (lo, hi) = loHi(c)
  And(C(">=", e, lo), C("<", e, hi))

proc rx(e: E; o: bool): string =
  template r(i: int): string = rx(e.a[i], o)
  case e.k
  of eLeaf: e.s
  of eBin: "(" & r(0) & " " & e.s & " " & r(1) & ")"
  of eCmp: r(0) & " " & e.s & " " & r(1)
  of eAnd: "(" & r(0) & " and " & r(1) & ")"
  of eOr: "(" & r(0) & " or " & r(1) & ")"
  of eNot: "not (" & r(0) & ")"
  of eCall: e.s & "(" & e.a.mapIt(rx(it, o)).join(", ") & ")"
  of eTrue: "true"
  of eFalse: "false"
  of eChk:
    let acc = e.s & "[" & r(0) & "] " & e.t
    if o: "(ok(" & $e.id & ", " & rx(bounds(e.s, e.a[0]), o) & ") and " & acc & ")" else: acc

proc chkIds(e: E): seq[int] =
  if e.k == eChk: result.add e.id
  for x in e.a: result.add chkIds(x)
proc unchk(e: E): E =
  if e.k == eChk: E(k: eFalse) else: E(k: e.k, s: e.s, t: e.t, id: e.id, a: e.a.mapIt(unchk it))

# ---- statement trees -----------------------------------------------------------

proc walk(n: Node): seq[Node] =
  result = @[n]
  for c in n.kids & n.els: result.add walk(c)
proc cp(n: Node): Node =
  result = Node()
  result[] = n[]
  result.kids = n.kids.mapIt(cp it)
  result.els = n.els.mapIt(cp it)
proc splice(l: var seq[Node]; n: Node; by: seq[Node]): bool =
  let j = l.find(n)
  if j >= 0:
    l.delete(j)
    l.insert(by, j)
  j >= 0
proc subst(root, n: Node; by: seq[Node] = @[]): bool =
  ## Replaces `n` by `by` wherever it hangs below `root` (deletes it by default).
  for par in walk(root):
    if splice(par.kids, n, by) or splice(par.els, n, by): return true
proc checkIds(p: Node): seq[(int, string)] =
  for n in walk(p):
    if n.k == nChk and n.ck != "assume": result.add (n.id, n.ck)
    for e in n.ex:
      for c in chkIds(e): result.add (c, "condidx")
  if p.ens != nil: result.add (p.ensid, "ensures")
proc hasId(n: Node; id: int): bool =
  (n.k == nChk and n.id == id) or (n.k == nProc and n.ensid == id and n.ens != nil) or
    n.ex.anyIt(id in chkIds(it))

proc chkCond(n: Node): E =
  ## The run-time condition a check node claims.
  let x = n.ex
  case n.ck
  of "assert", "assume": x[0]
  of "idx": bounds(n.cont, x[0])
  of "pos": C(">", x[0], N(0))
  of "between": And(C("<=", x[1], x[0]), C("<=", x[0], x[2]))
  of "rng": And(C(">=", x[0], N(0)), C("<=", x[0], N(8)))
  of "rnginc":
    let e = B("+", L("int(" & n.cont & ")"), N(n.step))
    And(C(">=", e, N(0)), C("<=", e, N(8)))
  else: C(">", L(n.cont & ".len"), N(0))   # pop

# ---- rendering ------------------------------------------------------------------

const
  Pre = """
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
  Head = ["var x = a", "var y = b", "var z = c", "var i = 0", "var j = 0", "var fuel = 0", "var w = u",
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
  Post = """
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

proc ad(res: var seq[Ln]; s: string; p: Node = nil; n: Node = nil) = res.add (s: s, p: p, n: n)

proc rn(n, p: Node; ind: string; o: bool; res: var seq[Ln])
proc rblk(ns: seq[Node]; p: Node; ind: string; o: bool; res: var seq[Ln]) =
  if ns.len == 0: res.ad(ind & "discard", p)
  for n in ns: rn(n, p, ind, o, res)

proc rn(n, p: Node; ind: string; o: bool; res: var seq[Ln]) =
  let x = n.ex.mapIt(rx(it, o))
  template line(s: string) = res.ad(ind & s, p, n)
  template sub(ns: seq[Node]) = rblk(ns, p, ind & "  ", o, res)
  case n.k
  of nS: line(n.fmt % x)
  of nChk:
    if not o:
      line(if n.ck == "assert": "{.assert: " & x[0] & ".}"
           elif n.ck == "assume": "{.assume: " & x[0] & ".}" else: n.fmt % x)
    elif n.ck == "assume":   # a false assumption is UB: this input proves nothing from here on
      line("if not (" & rx(chkCond(n), o) & "): (dead = true; return)")
    else:
      line("if bad(" & $n.id & ", " & rx(chkCond(n), o) & "): return")
      if n.ck != "assert": line(n.fmt % x)
  of nIf, nTry:
    line(if n.k == nIf: "if " & x[0] & ":" else: "try:")
    sub(n.kids)
    if n.hasEls:
      res.ad(ind & (if n.k == nIf: "else:" else: "except:"), p)
      sub(n.els)
  of nWhile:
    line("while " & x[0] & ":")
    if n.fuel != "":
      res.ad(ind & "  inc fuel", p)
      res.ad(ind & "  if fuel > 24: " & n.fuel, p)
    sub(n.kids)
  of nFor:
    line(n.fmt % x)
    sub(n.kids)
  of nCase:
    line("case " & x[0])
    for b in n.kids:
      res.ad(ind & "of " & b.fmt & ":", p)
      sub(b.kids)
    res.ad(ind & "else:", p)
    sub(n.els)
  of nProc, nOf: discard

proc render(ps: seq[Node]; o: bool; nch: int): (string, seq[Ln]) =
  ## Mode S (o = false) or O; returns the text and what each line belongs to.
  var res: seq[Ln]
  var hdr = "{.feature: \"" & (if o: "runtimeContracts" else: "staticContracts") &
            "\".}\n{.feature: \"assumeSync\".}\n" & Pre % (if o: "int" else: "range[0..8]")
  if o: hdr.add Harness % $max(nch, 1)
  for l in hdr.strip(leading = false).splitLines: res.ad(l)
  for p in ps:
    let pr = if p.ens != nil and not o: " {.ensures: " & rx(p.ens, o) & ".}" else: ""
    res.ad("proc p" & $p.id & "(" & Params & "): int" & pr & " =", p, p)
    for h in Head: res.ad("  " & h, p)
    rblk(p.kids, p, "  ", o, res)
    if o:
      let post = if p.ens == nil: "            discard rr"
                 else: Post % [$p.ensid, rx(p.ens, o).replace("result", "rr").replace("s.len", "ss[si].len")]
      let al = if p.fl == 'C': "0" else: "(si + (c and 3)) mod 3"
      for l in (Driver % [$p.id, al, post]).strip(leading = false).splitLines: res.ad(l)
  if o:
    for l in (Tail % $max(nch, 1)).strip(leading = false).splitLines: res.ad(l)
  res.ad("echo \"END\"")
  (res.mapIt(it.s).join("\n") & "\n", res)

# ---- generator ------------------------------------------------------------------

const
  Shared = ["gv", "tv", "go.f", "n", "q.f", "cx"]
  Writable = ["la", "t", "o.items", "o.arr"]

type Gen = object
  r: Rand
  a: bool                            ## flavour A
  lv, sq, gw, ct: seq[string]        ## lvalues, seqs, growable seqs, containers
  conds: seq[E]                      ## guards believed to hold here (invalidation ignored: that is the point)
  pairs, ptrs: seq[(string, string)] ## guarded (lvalue, container); (ptr, target)
  lets, nowrite, loopk: seq[string]
  nogrow, inloop, uniq, intry, ids: int

proc pick[T](g: var Gen; xs: openArray[T]): T = xs[g.r.rand(xs.high)]
proc ch(g: var Gen; p: float): bool = g.r.rand(1.0) < p
proc rf(g: var Gen; m = 1.0): float = g.r.rand(m)
proc fresh(g: var Gen; pf: string): string =
  inc g.uniq
  pf & $g.uniq
proc newid(g: var Gen): int =
  result = g.ids
  inc g.ids
proc last[T](xs: seq[T]; n: int): seq[T] = xs[max(0, xs.len - n) .. ^1]
proc writable(g: Gen): seq[string] = g.lv.filterIt(it notin g.nowrite)
proc st(fmt: string; ex: varargs[E]): Node = Node(k: nS, fmt: fmt, ex: @ex)
proc chk(g: var Gen; ck: string; ex: seq[E]; fmt = ""; cont = ""; step = 0): Node =
  Node(k: nChk, ck: ck, id: g.newid, ex: ex, fmt: fmt, cont: cont, step: step)

proc atom(g: var Gen): E =
  let q = g.rf
  if q < 0.45: L(g.pick(g.lv & @["a", "b", "c", "x", "i"] & g.lets & g.lets))
  elif q < 0.65: N(g.pick([-2, -1, 0, 0, 1, 1, 2, 3, 4, 5, 7, 8, 9, 10]))
  elif q < 0.82: L(g.pick(g.sq & @["st"]) & ".len")
  elif q < 0.90: L(g.pick(["int(u)", "int(w)", "int(r)", "int(o.cnt)", "high(s)", "high(t)", "int(u + 1'u8)",
                          "int(w - 1'u8)", "int(w * 2'u8)", "int(u and 7'u8)", "int(u shr 5)"]))
  elif g.ptrs.len > 0 and q < 0.95: L(g.pick(g.ptrs)[0] & "[]")
  else: L(g.pick(["a", "b", "x", "y"]))

proc intE(g: var Gen; d = 2): E =
  if d <= 0 or g.ch(0.35): return g.atom
  let q = g.rf
  if q < 0.30: B(g.pick(["+", "-"]), g.intE(d-1), g.pick([N(1), N(1), N(2), g.intE(d-1)]))
  elif q < 0.36: B("*", g.intE(d-1), N(g.pick([2, 3, -1])))
  elif q < 0.44: B("div", g.intE(d-1), N(g.pick([2, 3, 4])))
  elif q < 0.52: B("mod", g.intE(d-1), N(g.pick([2, 4, 5, 8])))
  elif q < 0.62: B("and", g.intE(d-1), N(g.pick([1, 3, 7, 7, 15, 255])))
  elif q < 0.68:
    var x = g.intE(d-1)
    if not g.a and x.k == eLeaf and x.s.startsWith("(-"): x = L(x.s[2 .. ^2])  # finding 02
    B("shr", x, N(g.pick([1, 2, 3])))
  elif q < 0.80: F(g.pick(["min", "max"]), g.intE(d-1), g.intE(d-1))
  elif q < 0.88: F(g.pick(if g.a: @["clamp7", "nonNeg", "abs", "abs"] else: @["clamp7", "nonNeg"]), g.intE(d-1))
  elif q < 0.93: B("-", B("-", L(g.pick(g.sq) & ".len"), N(1)), g.intE(d-1))
  else: g.atom

proc small(g: var Gen): E =
  ## Bounded and nonnegative: safe as a loop bound.
  let q = g.rf
  if q < 0.45: loHi(g.pick(g.ct))[1]
  elif q < 0.6: N(g.pick([0, 1, 3, 4, 6, 8, 9]))
  elif q < 0.8: B("and", g.intE(1), N(g.pick([3, 7, 15])))
  elif q < 0.9: F("clamp7", g.intE(1))
  else: B("-", loHi(g.pick(g.sq))[1], N(1))

proc cmpC(g: var Gen; d = 1): E =
  C(g.pick(["<", "<=", ">", ">=", "==", "!=", "<", ">="]), g.intE(d),
    g.pick([g.intE(d), g.atom, N(g.pick([0, 0, 1, 7, 8]))]))

proc guard(g: var Gen; v, c: string): E =
  ## `v` against the bounds of `c`, in one of the shapes the prover knows.
  let e = L(v)
  let (lo, hi) = loHi(c)
  let q = g.rf
  let lower = g.pick([C(">=", e, lo), C("<=", lo, e), C(">", e, B("-", lo, N(1))), C(">=", e, lo)])
  let upper = g.pick([C("<", e, hi), C("<=", e, B("-", hi, N(1))), C(">", hi, e), C("<", B("+", e, N(1)), hi),
                      C("<", e, B("-", hi, N(1))), C("<", e, hi)])
  if q < 0.55: And(lower, upper)
  elif q < 0.65: And(upper, lower)
  elif q < 0.75: Not(Or(C("<", e, lo), C(">=", e, hi)))
  elif q < 0.83: upper
  elif q < 0.90: lower
  else: And(And(lower, upper), g.cmpC)

proc cond(g: var Gen; d = 1): E =
  let q = g.rf
  if q < 0.5 or d <= 0: g.cmpC
  elif q < 0.7: And(g.cond(d-1), g.cond(d-1))
  elif q < 0.82: Or(g.cond(d-1), g.cond(d-1))
  elif q < 0.9: Not(g.cond(d-1))
  else: g.guard(g.pick(g.lv), g.pick(g.ct))

proc mutCond(g: var Gen; c: E): E =
  let q = g.rf
  case c.k
  of eCmp:
    let (l, r) = (c.a[0], c.a[1])
    if q < 0.3: c
    elif q < 0.5:
      C({"<": "<=", "<=": "<", ">": ">=", ">=": ">", "==": "<=", "!=": "<"}.toTable[c.s], l, r)
    elif q < 0.7:
      let k = N(g.pick([1, 1, 2, -1]))
      C(c.s, B("+", l, k), B("+", r, k))
    elif q < 0.85: C(c.s, B(g.pick(["+", "-"]), l, N(1)), r)
    else: C(c.s, l, B(g.pick(["+", "-"]), r, N(1)))
  of eAnd, eOr:
    if q < 0.35: g.mutCond(c.a[0])
    elif q < 0.7: g.mutCond(c.a[1])
    else: E(k: c.k, a: @[g.mutCond(c.a[0]), g.mutCond(c.a[1])])
  of eNot: (if q < 0.6: c else: g.mutCond(c.a[0]))
  else: c

proc claim(g: var Gen): E =
  let q = g.rf
  if g.conds.len > 0 and q < 0.5: return g.mutCond(g.pick(g.conds.last(4)))
  if g.pairs.len > 0 and q < 0.75:
    let (v, c) = g.pick(g.pairs.last(3))
    let hi = loHi(c)[1]
    let e = L(v)
    return g.pick([C("<", e, hi), C("<=", B("+", e, N(1)), hi), C(">", hi, N(0)), C(">", B("-", hi, e), N(0)),
      C(">=", B("-", B("-", hi, N(1)), e), N(0)), C(">=", e, N(0)), C("<", B("+", e, N(1)), hi),
      C("<", B("-", B("-", hi, N(1)), e), hi), C(">=", hi, N(1)), C(">", B("+", e, N(1)), e),
      C("<", B("-", e, N(1)), e), C(">=", B("*", e, N(2)), e), C("<=", B("div", e, N(2)), e),
      C("<", B("mod", e, N(8)), N(8))])
  if q < 0.85:
    let e = g.intE(1)
    if g.a and g.ch(0.3):
      return g.pick([C(">=", F("abs", e), N(0)), C(">=", F("abs", e), e), C("<=", B("and", F("abs", e), N(7)), N(7))])
    return g.pick([C(">", B("+", e, N(1)), e), C(">=", B("and", e, N(7)), N(0)), C("<=", B("and", e, N(7)), N(7)),
      C(">=", L(g.pick(g.sq) & ".len"), N(0)), C("<=", F("min", e, N(7)), N(7)), C(">=", F("max", e, N(0)), N(0)),
      C("<", B("mod", e, N(8)), N(8)), C(">=", B("mod", e, N(8)), N(0)), C("<=", B("shr", e, N(1)), e),
      C(">=", B("div", e, N(2)), N(0))])
  g.cond(1)

proc idxStmt(g: var Gen): Node =
  var c: string
  var e: E
  if g.pairs.len > 0 and g.ch(0.7):
    let pr = g.pick(g.pairs.last(3))
    c = if g.ch(0.2): g.pick(g.ct) else: pr[1]
    e = L(pr[0])
  else:
    c = g.pick(g.ct)
    e = L(g.pick(g.lv & g.lets))
  let hi = loHi(c)[1]
  let q = g.rf
  let ie =
    if q < 0.40: e
    elif q < 0.50: B("+", e, N(1))
    elif q < 0.58: B("-", e, N(1))
    elif q < 0.66: B("-", B("-", hi, N(1)), e)
    elif q < 0.72: B("and", g.intE(1), N(g.pick([3, 7])))
    elif q < 0.77: B("mod", e, if c in arrs: hi else: N(8))
    elif q < 0.82: F("clamp7", g.intE(1))
    elif q < 0.86: F("min", e, B("-", hi, N(1)))
    elif q < 0.90: B(g.pick(["div", "shr"]), e, N(g.pick([1, 2])))
    elif q < 0.94: B("+", e, L(g.pick(g.lv)))
    else: g.intE(2)
  if c == "st": g.chk("idx", @[ie], "result = result + ord(st[$1])", c)
  elif c in Writable and g.ch(0.3): g.chk("idx", @[ie, g.intE(1)], c & "[$1] = $2", c)
  else: g.chk("idx", @[ie], g.pick(g.writable & @["result", "result"]) & " = " & c & "[$1]", c)

proc barrier(g: var Gen): Node =
  ## A call or store that writes shared state (a func: only its var argument).
  let owned = ["x", "y", "z", "i", "j"].filterIt(it notin g.nowrite)
  var o = @["setGv($1)", "bumpGv()", "setTv($1)", "touchGo()", "clearGs()", "pokeP($1)", "poke(gb, $1)",
            "gfn($1)", "setCx($1)", "fn($1)", "q.f = $1", "n = $1", "gv = $1", "go.f = $1", "fadd(gs, $1)",
            "touchGo()", "setGv(1000000000)", "pokeP(-5)"]
  if g.nogrow > 0: o = o.filterIt("fadd" notin it)
  if g.nowrite.len > 0: o = o.filterIt("pokeP" notin it)  # a clean loop's counter may be the stashed address
  if owned.len > 0:
    let v = g.pick(owned)
    o.add ["mixG(" & v & ")", "fbump(" & v & ")", "fset(" & v & ", $1)", "fbump(" & v & ")"]
    if g.a: o.add ["stash(addr " & v & ")", "stash(addr " & v & ")", "stash(addr " & v & ")"]
  if g.a:
    let sh = g.writable.filterIt(it in Shared or it in ["o.f", "o.g"])
    if sh.len > 0:
      let v = g.pick(sh)
      o.add ["fbump(" & v & ")", "fset(" & v & ", $1)", "mixG(" & v & ")"]
  if "o.f" notin g.nowrite and "o.g" notin g.nowrite: o.add ["fclob(o)", "fclob(q)"]
  if g.nogrow == 0: o.add ["fadd(t, $1)", "fadd(o.items, $1)"]
  st(g.pick(o), g.intE(1))

proc mutation(g: var Gen): Node =
  let w = g.writable
  let q = g.rf
  if g.intry > 0 and g.ch(0.35): return st("risky($1)", g.intE(1))
  if g.ch(0.35): return g.barrier
  if w.len == 0: return st("result = $1", g.intE(1))
  var lv = g.pick(w)
  if g.pairs.len > 0 and g.ch(0.6):
    let cand = g.pairs.last(3).mapIt(it[0]).filterIt(it in w)
    if cand.len > 0: lv = g.pick(cand)
  if q < 0.22: return st(lv & " = $1", g.intE(2))
  if q < 0.36:
    return st(g.pick(["inc ~", "dec ~", "inc(~, 2)", "dec(~, 2)", "~ += $1", "~ -= $1"]).replace("~", lv), g.intE(1))
  if q < 0.40:
    let ps = g.ptrs.filterIt(it[1] notin g.nowrite)
    return if ps.len > 0: st(g.pick(ps)[0] & "[] = $1", g.intE(1)) else: st(lv & " = $1", g.intE(1))
  if q < 0.43 and g.a: return st("viaPtr(addr " & lv & ", $1)", g.intE(1))
  if q < 0.54: return st(g.pick(["inc ~", "dec ~", "~ = $1"]).replace("~", lv), g.intE(1))
  if q < 0.62: return st("bump(" & lv & ")")
  if q < 0.68: return st("setTo(" & lv & ", $1)", g.intE(1))
  if q < 0.74 and w.len > 1: return st("swap(" & lv & ", " & g.pick(w.filterIt(it != lv)) & ")")
  if q < 0.90:
    var c = g.pick(g.gw)
    if g.pairs.len > 0 and g.ch(0.6):
      let cand = g.pairs.last(3).mapIt(it[1]).filterIt(it in g.gw)
      if cand.len > 0: c = g.pick(cand)
    var o = @["~.setLen(" & $g.pick([0, 0, 1, 2, 3]) & ")", "shrink(~)", "dropOne(~)", "~ = @[]", "~ = s",
              "clobber(o)", "o = Obj()", "swap(t, o.items)", "discard ~.pop()"]
    if g.nogrow == 0: o.add ["~.add $1", "~.add $1", "~.setLen(" & $g.pick([5, 9]) & ")"]
    let s = g.pick(o).replace("~", c)
    if "pop" in s: return g.chk("pop", @[], s, c)
    if ("o.f" in g.nowrite or "o.g" in g.nowrite) and ("clobber" in s or "Obj()" in s):
      return st("dropOne(" & c & ")")
    return st(s, g.intE(1))
  if q < 0.95: return st("w = " & g.pick(["w + 1'u8", "w - 1'u8", "uint8($1 and 255)", "w * 3'u8"]), g.intE(1))
  st("result = $1", g.intE(2))

proc stmt(g: var Gen; depth: int): seq[Node]
proc blk(g: var Gen; depth, n: int): seq[Node] =
  ## `n` statements; facts and names introduced here go out of scope at the end.
  let sv = (g.conds.len, g.pairs.len, g.lets.len, g.ptrs.len)
  for _ in 0 ..< n: result.add g.stmt(depth)
  g.conds.setLen sv[0]
  g.pairs.setLen sv[1]
  g.lets.setLen sv[2]
  g.ptrs.setLen sv[3]
proc body(g: var Gen; depth: int; xc: seq[E] = @[]; xp: seq[(string, string)] = @[]): seq[Node] =
  let (a, b) = (g.conds.len, g.pairs.len)
  g.conds.add xc
  g.pairs.add xp
  result = g.blk(depth - 1, g.r.rand(1..4))
  g.conds.setLen a
  g.pairs.setLen b

proc stmt(g: var Gen; depth: int): seq[Node] =
  var q = g.rf(100)
  if depth <= 0 and q >= 62: q = g.rf(62)
  let nobrk = not g.a and g.loopk.len > 0 and g.loopk[^1] == "for"   # finding 01
  # ---- leaves
  if q < 16: return @[g.idxStmt]
  if q < 28: return @[g.chk("assert", @[g.claim])]
  if q < 31:
    if g.ch(0.6): return @[g.chk("pos", @[g.intE(1)], g.pick(g.writable & @["result"]) & " = needsPos($1)")]
    return @[g.chk("between", @[g.intE(1), g.intE(0), g.intE(0)], "result = needsRange($1, $2, $3)")]
  if q < 36:
    let qq = g.rf
    if qq < 0.4: return @[g.chk("rng", @[g.intE(1)], g.pick(["r", "o.cnt"]) & " = $1")]
    if qq < 0.7:
      let step = g.pick([1, 1, -1, 2])
      let t = g.pick(["r", "r", "o.cnt"])
      let f = if step == 1: "inc " & t elif step == -1: "dec " & t else: "inc(" & t & ", 2)"
      return @[g.chk("rnginc", @[], f, t, step)]
    return @[g.chk("rng", @[g.intE(1)], "result = takesRT($1)")]
  if g.ch(0.10):   # a barrier, then restate a guard in scope (true before the barrier)
    result = @[g.barrier]
    if g.conds.len > 0: result.add g.chk("assert", @[g.pick(g.conds.last(4))])
    return
  if q < 38:
    let c = g.claim
    g.conds.add c
    return @[g.chk("assume", @[c])]
  if q < 52: return @[g.mutation]
  if q < 56:
    let nm = g.fresh("l")
    result = @[st("let " & nm & " = $1", g.intE(2))]
    g.lets.add nm
    return
  if q < 58 and g.a:
    let nm = g.fresh("p")
    let t = g.pick(g.lv)
    g.ptrs.add (nm, t)
    return @[st("let " & nm & " = addr " & t)]
  if q < 60:
    if g.inloop > 0 and g.nowrite.len == 0 and g.ch(0.7):
      return @[st(if nobrk: "continue" else: g.pick(["break", "continue"]))]
    if g.inloop > 0 and g.ch(0.5) and not nobrk: return @[st("break")]
    return @[Node(k: nIf, ex: @[g.cond(1)], kids: @[st("return")])]
  if q < 62: return @[st("result = $1", g.intE(2))]
  # ---- compound
  if q < 74:   # guarded use
    let v = g.pick(g.lv & g.lets)
    let c = g.pick(g.ct)
    let gd = g.guard(v, c)
    let kids = g.body(depth, @[gd], @[(v, c)])
    let e = g.ch(0.25)
    return @[Node(k: nIf, ex: @[gd], kids: kids, hasEls: e, els: if e: g.body(depth) else: @[])]
  if q < 79:   # random if
    let c = g.cond(2)
    let kids = g.body(depth, @[c])
    let e = g.ch(0.4)
    return @[Node(k: nIf, ex: @[c], kids: kids, hasEls: e, els: if e: g.body(depth, @[Not(c)]) else: @[])]
  if q < 84:   # guard clause
    let v = g.pick(g.lv & g.lets)
    let c = g.pick(g.ct)
    let (lo, hi) = loHi(c)
    let e = L(v)
    let neg = g.pick([Or(C("<", e, lo), C(">=", e, hi)), C(">=", e, hi), C("<", e, lo), Not(g.guard(v, c))])
    g.conds.add(if neg.k == eNot: neg.a[0] else: Not(neg))
    g.pairs.add (v, c)
    let ex = g.pick(["return", "return", if g.inloop > 0 and not nobrk: "break" else: "return"])
    return @[Node(k: nIf, ex: @[neg], kids: @[st(ex)])]
  if q < 91:   # counting while loop; a clean one writes neither its counter nor grows a seq
    let w = g.writable.filterIt(it in ["i", "j", "x", "y", "z"])
    if w.len == 0: return @[g.mutation]
    let v = g.pick(w)
    let c = g.pick(g.ct)
    let (lo, hi) = loHi(c)
    let e = L(v)
    let down = g.ch(0.25)
    let clean = g.ch(0.5)
    var init, step: Node
    var cd: E
    if down:
      init = st(v & " = $1", B("-", hi, N(1)))
      cd = g.pick([C(">=", e, lo), C(">", e, B("-", lo, N(1)))])
      step = st(g.pick(["dec ~", "~ = ~ - 1", "dec ~"]).replace("~", v))
    else:
      init = st(v & " = $1", g.pick([lo, lo, N(0), N(1), B("and", g.intE(1), N(3))]))
      cd = g.pick([C("<", e, hi), C("<", e, hi), C("<=", e, B("-", hi, N(1))), C("<", B("+", e, N(1)), hi),
                   C(if clean: "<" else: "!=", e, hi)])
      step = st(g.pick(["inc ~", "inc ~", "~ = ~ + 1", "inc(~, 2)", "~ += 1"]).replace("~", v))
    if c != "st" and g.ch(0.25):
      cd = And(cd, E(k: eChk, id: g.newid, s: c, t: g.pick(["!=", "==", ">", "<"]) & " " & $g.pick([0, 3, 5]),
                     a: @[e]))
    elif g.ch(0.15): cd = And(cd, g.cmpC)
    inc g.inloop
    g.loopk.add "while"
    if clean:
      g.nowrite.add v
      inc g.nogrow
    var kids = g.body(depth, @[cd], @[(v, c)])
    if clean:
      discard g.nowrite.pop
      dec g.nogrow
    dec g.inloop
    discard g.loopk.pop
    if clean or g.ch(0.9): kids.add step
    return @[init, Node(k: nWhile, ex: @[cd], kids: kids, fuel: if clean: "" else: g.pick(["break", "break", "return"]))]
  if q < 97:   # for loop
    let kv = g.fresh("k")
    let c = g.pick(g.ct)
    let (lo, hi) = loHi(c)
    let qq = g.rf
    var fmt: string
    var ex: seq[E]
    if qq < 0.45:
      fmt = "for " & kv & " in $1 ..< $2:"
      ex = @[g.pick([lo, lo, N(0), N(1)]), g.pick([hi, hi, g.small])]
    elif qq < 0.75:
      fmt = "for " & kv & " in $1 .. $2:"
      ex = @[g.pick([lo, N(0), N(1)]), g.pick([B("-", hi, N(1)), B("-", hi, N(1)), g.small])]
    else:
      fmt = "for " & kv & " in countdown($1, $2):"
      ex = @[g.pick([B("-", hi, N(1)), g.small]), g.pick([lo, N(0), N(1)])]
    g.lets.add kv
    inc g.inloop
    g.loopk.add "for"
    let kids = g.body(depth, @[], @[(kv, c)])
    discard g.loopk.pop
    dec g.inloop
    g.lets.delete(g.lets.find(kv))
    return @[Node(k: nFor, fmt: fmt, ex: ex, kids: kids)]
  if q < 98.5:   # try/except around risky(); flavour C: the try body writes nothing (finding 08)
    inc g.intry
    let n0 = g.nowrite.len
    if not g.a:
      g.nowrite.add g.lv
      inc g.nogrow
    var kids = g.body(depth)
    if not g.a:
      g.nowrite.setLen n0
      dec g.nogrow
    dec g.intry
    kids.insert(st("risky($1)", g.intE(1)), g.r.rand(kids.len))
    return @[Node(k: nTry, kids: kids, hasEls: true, els: g.body(depth))]
  # case with ranges
  let v = g.pick(g.lv)
  let e = L(v)
  var cuts = toSeq(-1 .. 9)
  g.r.shuffle(cuts)
  cuts = cuts[0 ..< g.r.rand(2..4)].sorted
  var brs: seq[Node]
  for bi in 0 ..< cuts.len - 1:
    let lo = cuts[bi]
    var hi = cuts[bi + 1] - 1
    var lab: string
    if hi > lo and g.ch(0.8): lab = N(lo).s & ".." & $hi
    elif hi == lo + 1: lab = N(lo).s & ", " & $hi
    else:
      hi = lo
      lab = N(lo).s
    brs.add Node(k: nOf, fmt: lab, kids: g.body(depth, @[And(C(">=", e, N(lo)), C("<=", e, N(hi)))],
                                              @[(v, g.pick(["ar", "la", "o.arr"]))]))
  @[Node(k: nCase, ex: @[e], kids: brs, hasEls: true, els: if g.ch(0.5): g.body(depth) else: @[])]

proc genProc(seed, idx: int; fl: char; ids: var int): Node =
  var g = Gen(r: initRand(seed), a: fl == 'A', ids: ids, lv: @["x", "y", "z", "i", "j", "o.f", "o.g"],
              sq: @["s", "t", "o.items"], gw: @["t", "o.items"],
              ct: @["ar", "ar", "la", "o.arr", "s", "s", "t", "t", "o.items", "st"])
  if g.a:
    g.lv.add Shared
    for x in [addr g.sq, addr g.gw, addr g.ct]: x[].add ["gs", "q.items"]
  result = Node(k: nProc, id: idx, fl: fl, ensid: -1, kids: g.blk(3, g.r.rand(3..7)))
  if g.ch(0.3):
    let res = L("result")
    if g.ch(0.5):   # make the claim plausible: set result from a bounded expression last
      result.kids.add st("result = $1", g.pick([F("clamp7", g.intE(1)), B("and", g.intE(1), N(7)),
        F("nonNeg", g.intE(1)), L("s.len"), F("min", L("a"), L("b")), B("+", L("a"), N(1)),
        B("mod", g.intE(1), N(8)), B("div", L("a"), N(2))]))
    result.ens = g.pick([C(">=", res, N(0)), C("<=", res, N(7)), And(C(">=", res, N(0)), C("<=", res, N(7))),
      C("<=", res, L("a")), C("<", res, L("s.len")), C("<=", res, L("s.len")), C(">", res, L("a")),
      C("<", res, N(8)), C(">=", res, N(-7)), C("<=", res, L("b")), Or(C(">=", res, N(0)), C("<", L("a"), N(0)))])
    result.ensid = g.newid
  ids = g.ids

# ---- func rule (4ba90a78) ------------------------------------------------------

const
  FPre = """
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
  FMsg = "through a ref/ptr in a `.noSideEffect` context"
  # (param decl, prologue, head expr, type, head is mutable)
  Heads = [("h: var Holder", "", "h", "Holder", true), ("h: var Holder", "", "h", "Holder", true),
    ("h: var Holder", "", "h", "Holder", true), ("h: Holder", "var c = h", "c", "Holder", true),
    ("h: Holder", "", "h", "Holder", false), ("n: var Node", "", "n", "Node", true), ("n: Node", "", "n", "Node", false),
    ("p: ptr Plain", "", "p", "PPlain", false), ("p: var ptr Plain", "", "p", "PPlain", true),
    ("s: var seq[Node]", "", "s", "SeqNode", true), ("s: var seq[Plain]", "", "s", "SeqPlain", true),
    ("a: var array[2, Node]", "", "a", "ArrNode", true), ("o: var openArray[int]", "", "o", "OAInt", true),
    ("pl: var Plain", "", "pl", "Plain", true), ("t: var Tup", "", "t", "Tup", true)]
let tys = {"Holder": "obj x:int r:Node p:PPlain pl:Plain s:SeqInt rs:SeqNode ps:SeqPlain arr:ArrInt ra:ArrNode t:Tup ua:UA",
  "Plain": "obj x:int arr:ArrInt s:SeqInt", "NodeObj": "obj x:int s:SeqInt pl:Plain", "Tup": "obj a:int r:Node",
  "Node": "ref NodeObj", "PPlain": "ptr Plain", "SeqInt": "seq int", "SeqNode": "seq Node", "SeqPlain": "seq Plain",
  "ArrInt": "arr int", "ArrNode": "arr Node", "OAInt": "arr int", "UA": "ua int", "int": "int"}.toTable

proc fwalk(r: var Rand; ty0, path0: string; steps: int): (string, string, bool, string) =
  ## A random access path. Shape letters: f field, R field through ref/ptr, D `[]`, E element, U UncheckedArray.
  var (ty, path, behind, shape) = (ty0, path0, false, "")
  for _ in 0 ..< steps:
    let w = tys[ty].split(' ')
    var f: seq[string]
    case w[0]
    of "int": break
    of "obj":
      f = r.sample(w[1 .. ^1]).split(':')
      shape.add 'f'
    of "ref", "ptr":
      behind = true
      if r.rand(1.0) < 0.3:
        path.add "[]"
        ty = w[1]
        shape.add 'D'
      else:
        f = r.sample(tys[w[1]].split(' ')[1 .. ^1]).split(':')
        shape.add 'R'
    else:
      path.add "[0]"
      ty = w[1]
      behind = behind or w[0] == "ua"
      shape.add(if w[0] == "ua": 'U' else: 'E')
    if f.len > 0:
      path.add "." & f[0]
      ty = f[1]
    if r.rand(1.0) < 0.25: break
  (path, ty, behind, shape)

proc writesFor(ty, p: string): seq[string] =
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

type FC = tuple[text: string, legal: bool, why, form: string]
proc fcase(r: var Rand; i: int): FC =
  ## One routine whose legality follows from the func rule alone.
  for _ in 0 ..< 50:
    let (decl, pro, head, ty, mut) = r.sample(Heads)
    let (path, pty, behind, sh) = fwalk(r, ty, head, r.rand(4))
    let shape = if sh == "": "-" else: sh
    let kind = r.sample(["func", "func", "func", "nse", "iter", "proc", "fse", "castfunc", "varres", "varres"])
    if not mut and not behind: continue   # immutable for another reason: not this rule
    if kind == "varres":
      if pty != "int" or ": var " notin decl or pro != "": continue
      let rk = r.sample(["func", "nse", "proc"])
      let form = r.sample(["expr", "return", "result"])
      let hdr = (if rk == "func": "func c" else: "proc c") & $i & "(" & decl & "): var int" &
                (if rk == "nse": " {.noSideEffect.}" else: "") & " ="
      let text = if form == "expr": hdr & " " & path & "\n"
                 else: hdr & "\n  " & (if form == "return": "return " else: "result = ") & path & "\n"
      return (text, not behind or rk == "proc", "var-result " & rk & " behind=" & $behind & " " & form,
              "varres-" & form & " path=" & shape)
    let ws = writesFor(pty, path)
    if ws.len == 0: continue
    let w = r.sample(ws)
    if ty == "OAInt" and (w.endsWith(".add 1") or "setLen" in w or "= @[]" in w or "fsq" in w): continue
    let be = behind or w.startsWith("let q = addr")   # q[] is a dereference
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
    let op = if w.startsWith(path): w[path.len .. ^1].splitWhitespace[0] else: w.split('(')[0].split(' ')[0]
    return (text, not be or kind notin ["func", "nse", "iter"], kind & " behind=" & $be & " head=" & decl,
            op & " path=" & shape)

proc frender(cs: seq[FC]): (string, seq[(int, int)]) =
  var ls = FPre.strip(leading = false).splitLines
  for c in cs:
    let lo = ls.len + 1
    ls.add c.text.strip(leading = false).splitLines
    result[1].add (lo, ls.len)
  result[0] = ls.join("\n") & "\n"

# ---- running ---------------------------------------------------------------------

type
  Err = tuple[ln, col: int, msg: string]
  Run = tuple[st: string, R, P, F: seq[int], W: Table[int, string], o: string]

proc build(src, name, cmd: string): (int, string) =
  writeFile(wd / name & ".nim", src)
  let c = "cd " & quoteShell(wd) & " && timeout -k 5 180 " & quoteShell(nimony) & " " & cmd &
          " --nimcache:nc_" & name & " " & name & ".nim"
  for _ in 0 .. 1:
    let (o, rc) = execCmdEx(c)
    result = (rc, o)
    if rc == 0 or "deps.nif" notin o: break   # known flake (report 08): retry once

proc errs(o, name: string): seq[Err] =
  ## `file(line, col) Error: msg`; an error in another file gets line 0.
  for l in o.splitLines:
    let k = l.find(") Error: ")
    if k < 0: continue
    let b = l.rfind('(', last = k)
    let nums = l[b + 1 ..< k].split(", ")
    if b < 0 or nums.len != 2 or not nums.allIt(it.len > 0 and it.allCharsInSet(Digits)): continue
    var m = l[k + 9 .. ^1]
    let v = m.find(" [pass --verbose")
    if v >= 0: m.setLen v
    result.add ((if l[0 ..< b].endsWith(name & ".nim"): parseInt(nums[0]) else: 0), parseInt(nums[1]), m)

proc proverMsg(m: string): bool =
  ["cannot prove", "violated", "value out of range", "unexpectedly"].anyIt(it in m)
proc crashy(o: string): bool =
  let t = o.splitLines.filterIt(") Error: " notin it and "nifmake: command failed" notin it and
                                not it.startsWith("FAILURE")).join("\n").toLowerAscii
  ["assertiondefect", "traceback", "sigsegv", "illegal storage", " bug", "unreachable", "indexdefect",
   "out of bounds", "signal", "[assert"].anyIt(it in t)

proc runO(src, name: string): Run =
  ## Compile in mode O and run; the program prints R/P/F <id> (reached/passed/failed) and W <id> <input>.
  let (rc, o) = build(src, name, "c")
  result.o = o
  result.st = if rc in [124, 137]: "timeout" else: "fail"
  if rc != 0: return
  var exe = ""
  for f in walkDirRec(wd / "nc_" & name):
    if f.extractFilename == name: exe = f
  let (o2, rc2) = execCmdEx("timeout -k 2 60 " & quoteShell(exe))
  result.o = o2
  if rc2 in [124, 137]: result.st = "timeout"
  for l in o2.splitLines:
    if l == "END" and rc2 == 0: result.st = "ok"
    elif l.len > 2 and l[0] in "RPFW" and l[1] == ' ':
      let w = l.split(' ', 2)
      let id = parseInt(w[1])
      case l[0]
      of 'R': result.R.add id
      of 'P': result.P.add id
      of 'F': result.F.add id
      else: result.W[id] = w[2]

proc report(kind: string; s, id: int; sig, src, txt: string): string =
  result = outDir / kind & "_" & $s & "_" & $id
  writeFile(result & ".nim", src)
  if txt != "": writeFile(result & ".txt", txt & "\n")
  let f = outDir / "log.csv"
  let hdr = not fileExists(f)
  let h = open(f, fmAppend)
  if hdr: h.write "time_s,programs,finding_id,signature\n"
  h.write formatFloat(epochTime() - t0, ffDecimal, 1) & "," & $np & "," & result.extractFilename & "," &
          sig.replace(",", ";") & "\n"
  h.close
  echo "  ", kind, ": ", sig

# ---- oracle ------------------------------------------------------------------------

proc settle(ps: var seq[Node]; nch: int; rej: var Table[int, (int, string)]): (string, string, string) =
  ## Deletes every claim the prover rejects until the module compiles; rej[id] = (round, message).
  for rnd in 0 ..< 10:
    let (src, lm) = render(ps, false, nch)
    let (rc, o) = build(src, "s", "c")
    if rc == 0: return ("ok", src, o)
    if rc in [124, 137]: return ("timeout", src, o)
    let es = errs(o, "s")
    if es.len == 0 or crashy(o): return ("crash", src, o)
    var progress = false
    var drop: seq[Node]
    for e in es:
      if e.ln < 1 or e.ln > lm.len or lm[e.ln - 1].p == nil: continue
      let (p, n) = (lm[e.ln - 1].p, lm[e.ln - 1].n)
      if proverMsg(e.msg) and "postcondition" in e.msg:
        if p.ens != nil:
          discard rej.hasKeyOrPut(p.ensid, (rnd, e.msg))
          p.ens = nil
          progress = true
      elif not proverMsg(e.msg) or n == nil:
        if p notin drop: drop.add p
      elif n.k == nChk and n.ck != "assume":
        discard rej.hasKeyOrPut(n.id, (rnd, e.msg))
        if subst(p, n): progress = true
      elif n.k in {nIf, nWhile} and chkIds(n.ex[0]).len > 0:
        for c in chkIds(n.ex[0]): discard rej.hasKeyOrPut(c, (rnd, e.msg))
        n.ex[0] = unchk(n.ex[0])
        progress = true
      elif n.k in {nS, nChk} and subst(p, n): progress = true
      elif p notin drop: drop.add p
    for p in drop: ps.delete(ps.find(p))
    if not progress and drop.len == 0: return ("stuck", src, o)
  ("rounds", "", "")

proc hasWord(s, w: string): bool =
  var i = s.find(w)
  while i >= 0:
    if (i == 0 or s[i-1] notin IdentChars) and (i + w.len >= s.len or s[i + w.len] notin IdentChars): return true
    i = s.find(w, i + 1)

proc tags(p: Node; cid, nch: int): string =
  ## Classifier: the shared variables the failing claim names + the known-bug constructs in the proc.
  let (src, lm) = render(@[p], false, nch)
  let claim = if p.ensid == cid: "result" else: lm.filterIt(it.n != nil and hasId(it.n, cid)).mapIt(it.s).join(" ")
  var t: seq[string]
  for v in ["gv", "tv", "go", "gs", "n", "q", "cx", "o", "t"]:
    if hasWord(claim, v): t.add "claim-" & v
  let ls = src[src.find("proc p" & $p.id & "(") .. ^1].splitLines.mapIt(it.strip)
  var inFor, fb: bool
  for l in ls:
    if l.startsWith("for "): inFor = true
    if inFor and hasWord(l, "break"): fb = true
  if fb: t.add "forbreak"
  if ls.anyIt("(-1) shr" in it or "(-2) shr" in it): t.add "negshr"
  if ls.anyIt("abs(" in it): t.add "abs"
  if ls.anyIt((it.startsWith("let p") and " = addr " in it) or "viaPtr(addr" in it): t.add "addr"
  if ls.anyIt("stash(" in it): t.add "stash"
  if ls.anyIt(it == "try:"): t.add "try"
  if t.len == 0: "none" else: t.join("+")

proc pred(kind: string; cid, nch: int): proc (p: Node): bool =
  ## Does the finding persist for the single proc `p`?
  result = proc (p: Node): bool =
    let (src, lm) = render(@[p], false, nch)
    let (rc, o) = build(src, "ms", "c")
    if kind == "unsound":
      if rc != 0: return false
    else:   # false-violation: the same rejection and nothing else, and the claim passes at run time
      let es = errs(o, "ms")
      let same = if p.ensid == cid: p.ens != nil and es.anyIt("postcondition violated" in it.msg)
                 else: es.anyIt(it.ln in 1 .. lm.len and lm[it.ln - 1].n != nil and hasId(lm[it.ln - 1].n, cid) and
                                ("violated" in it.msg or "out of range" in it.msg))
      if not same or es.anyIt(not proverMsg(it.msg)): return false
    let r = runO(render(@[p], true, nch)[0], "mo")
    r.st == "ok" and cid in (if kind == "unsound": r.F else: r.P)

# ---- reduction ----------------------------------------------------------------------

proc cands(e: E): seq[E] =
  ## Smaller expressions of the same type for `e` or any sub-expression.
  if e.isBool:
    if e.k in {eAnd, eOr, eNot}: result.add e.a
    if e.k notin {eTrue, eCmp}: result.add E(k: eTrue)
  else:
    if e.k in {eBin, eCall}: result.add e.a
    if e.k != eLeaf: result.add N(0)
  for i in 0 ..< e.a.len:
    for x in cands(e.a[i]):
      let y = E(k: e.k, s: e.s, t: e.t, id: e.id, a: e.a)
      y.a[i] = x
      result.add y

proc unwrap(q: Node; i, v: int): bool =
  ## Variant v of simplifying node i: replace it by its v-th body (0..2), or drop else/fuel (3), ensures (proc).
  let ns = walk(q)
  if i >= ns.len: return false
  let n = ns[i]
  if n.k == nProc:
    result = v == 0 and n.ens != nil
    if result: n.ens = nil
  elif v == 3:
    if n.k == nIf and n.hasEls:
      n.hasEls = false
      n.els = @[]
      return true
    if n.k == nWhile and n.fuel != "":
      n.fuel = ""
      return true
  else:
    let ls = case n.k
      of nCase: n.kids.mapIt(it.kids) & @[n.els]
      of nIf, nTry: (if n.hasEls: @[n.kids, n.els] else: @[n.kids])
      of nWhile, nFor: @[n.kids]
      else: @[]
    if v < ls.len: return subst(q, n, ls[v])

proc reduce(p0: Node; still: proc (p: Node): bool): Node =
  var p = p0
  var tests = 0
  proc tryIt(m: proc (q: Node): bool): bool =
    if tests >= budget: return false
    let q = cp(p)
    if not m(q): return false
    inc tests
    result = still(q)
    if result: p = q
  var changed = true
  while changed and tests < budget:
    changed = false
    var i = 1
    while i < walk(p).len:   # delete statements (parents first: a whole subtree in one test)
      if tryIt(proc (q: Node): bool =
          let ns = walk(q)
          i < ns.len and ns[i].k != nOf and subst(q, ns[i])): changed = true
      else: inc i
    i = walk(p).len - 1
    while i >= 0:   # unwrap compound statements, drop else/fuel/ensures
      for v in 0 .. 3:
        if tryIt(proc (q: Node): bool = unwrap(q, i, v)):
          changed = true
          break
      i = min(i, walk(p).len) - 1
    i = walk(p).len - 1
    while i >= 0:   # simplify expressions
      for ei in 0 ..< walk(p)[i].ex.len:
        var again = true
        while again and tests < budget:
          again = false
          for c in cands(walk(p)[i].ex[ei]):
            let cc = c
            if tryIt(proc (q: Node): bool =
                walk(q)[i].ex[ei] = cc
                true):
              changed = true
              again = true
              break
      dec i
  p

proc reduceTo(base: string; p: Node; still: proc (p: Node): bool; nch: int) =
  if not doReduce: return
  if not still(p):
    echo "  not reproduced standalone"
    return
  let q = reduce(p, still)
  writeFile(base & ".reduced.nim", render(@[q], false, nch)[0])
  echo "  reduced ", walk(p).len, " -> ", walk(q).len, " nodes: ", base, ".reduced.nim"

# ---- batches ----------------------------------------------------------------------

proc soundBatch(s: int): int =
  let fl = if s mod 3 == 0: 'A' else: 'C'
  var ids = 0
  var ps: seq[Node]
  for i in 0 ..< 16: ps.add genProc(s * 1000 + i + 1, i, fl, ids)
  np += 16
  let nch = ids
  let orig = ps.mapIt(cp it)
  var kinds = initTable[int, string]()
  for p in orig:
    for (id, k) in checkIds(p): kinds[id] = k
  var rej = initTable[int, (int, string)]()
  let (st, src, o) = settle(ps, nch, rej)
  if st != "ok":
    discard report(if st == "crash": "crash" else: "odd", s, 0, (if st == "crash": "crash" else: "odd:settle-" & st), src, o)
    return 1
  var owner = initTable[int, Node]()
  for p in ps:
    for (id, _) in checkIds(p): owner[id] = p
  let r = runO(render(ps, true, nch)[0], "o")
  echo "seed ", s, " ", fl, ": ", ps.len, " procs, ", kinds.len, " checks, ", rej.len, " rejected, ", owner.len,
       " proved, oracle ", r.st
  if r.st != "ok":
    discard report("odd", s, 0, "odd:oracle-" & r.st, render(ps, true, nch)[0], r.o)
    return 1
  for cid in r.F.sorted:
    if cid notin owner: continue
    let p = owner[cid]
    let base = report("unsound", s, cid, "unsound/" & fl & ":" & kinds[cid] & ":" & tags(p, cid, nch),
                      render(@[p], false, nch)[0], r.W.getOrDefault(cid))
    inc result
    reduceTo(base, p, pred("unsound", cid, nch), nch)
  if rej.len == 0: return
  # the reverse direction, on the original module
  let r2 = runO(render(orig, true, nch)[0], "o2")
  if r2.st != "ok": return
  var oo = initTable[int, Node]()
  for p in orig:
    for (id, _) in checkIds(p): oo[id] = p
  for cid in toSeq(rej.keys).sorted:
    let (rnd, msg) = rej[cid]
    if rnd != 0 or cid notin oo: continue
    if "cannot prove" in msg:
      if cid in r2.R and cid notin r2.F:
        let h = open(outDir / "incomplete.log", fmAppend)
        h.write $s & "\t" & kinds[cid] & "\t" & msg & "\n"
        h.close
    elif cid in r2.P and kinds[cid] != "ensures":   # (an ensures is judged per `return`, the oracle sees the proc)
      let base = report("false-violation", s, cid, "false-violation:" & kinds[cid] & ":" & msg.split(':')[0],
                        render(@[oo[cid]], false, nch)[0], msg)
      inc result
      reduceTo(base, oo[cid], pred("false-violation", cid, nch), nch)

proc funcBatch(s: int): int =
  var r = initRand(s)
  var cs: seq[FC]
  for i in 0 ..< 40:
    let c = fcase(r, i)
    if c.text != "": cs.add c
  np += cs.len
  let (src, rg) = frender(cs)
  let (rc, o) = build(src, "f", "check")
  let es = errs(o, "f")
  if rc in [124, 137] or (rc != 0 and es.len == 0):
    discard report("func-crash", s, 0, "func-crash:" & $rc, src, o)
    return 1
  var per = initTable[int, seq[string]]()
  if es.anyIt(it.ln == 0 or FMsg notin it.msg):
    # another error can stop the pass that checks the rule: judge each routine on its own
    for i, c in cs:
      let (t1, r1) = frender(@[c])
      let (rc1, o1) = build(t1, "f1", "check")
      let e1 = errs(o1, "f1")
      if rc1 in [124, 137] or (rc1 != 0 and e1.len == 0):
        discard report("func-crash", s, i, "func-crash:" & $rc1, t1, o1)
        inc result
      else: per[i] = e1.filterIt(it.ln == 0 or it.ln in r1[0][0] .. r1[0][1]).mapIt(it.msg)
  else:
    for i in 0 ..< cs.len: per[i] = es.filterIt(it.ln in rg[i][0] .. rg[i][1]).mapIt(it.msg)
  for i, c in cs:
    if i notin per: continue
    let ms = per[i]
    let fr = ms.filterIt(FMsg in it)
    let ot = ms.filterIt(FMsg notin it)
    let kind = if not c.legal and ms.len == 0: "func-accepts-invalid"
               elif c.legal and ms.len > 0: "func-rejects-valid"
               elif not c.legal and ot.len > 0 and fr.len == 0: "func-other-error"
               else: ""
    if kind == "": continue
    var sig = kind & ":" & c.why & " " & c.form
    if ms.len > 0:   # the message with its access paths blanked
      sig.add ":" & (if ot.len > 0: ot else: fr)[0].split(' ').mapIt(
        (let w = it.strip(chars = {'`', '\''}); if w.len > 0 and w[0] in {'a'..'z'} and
          ('.' in w or '[' in w): "PATH" else: it)).join(" ")
    discard report(kind, s, i, sig, frender(@[c])[0], ms.join("\n"))
    inc result
  echo "seed ", s, " F: ", cs.len, " routines, ", result, " findings"

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
  wd = absolutePath(work) / ("w" & $seed)
  createDir(outDir)
  createDir(wd)
  var found = 0
  var k = 0
  while k < count and (minutes == 0 or epochTime() - t0 < minutes * 60):
    let s = seed + k
    found += (if s mod 3 == 2: funcBatch(s) else: soundBatch(s))
    inc k
  var ru: Rusage
  discard getrusage(RUSAGE_CHILDREN, addr ru)
  let cpu = cpuTime() + float(ru.ru_utime.tv_sec) + float(ru.ru_stime.tv_sec)
  echo k, " modules, ", np, " programs, ", found, " findings, wall ", int(epochTime() - t0), " s, cpu ", int(cpu),
       " s - ", outDir

main()
