## Memory-management fuzzer for nimony's hexer passes (duplifier, destroyer,
## lifter, mover, arcopt) under ARC and ORC.
##
## Programs are random statements over a hook-counting object `R(id, v)`.
## Every id lives in a global table (never / alive / dead) and the hooks
## check it: `=destroy` of a dead id, `=copy`/`=dup` from a dead id, or
## `get()` of a moved or dead value prints `ERR ...`; at exit every id must
## be dead (`LEAK id=...`) and a `SUMMARY` line prints the counts. So the
## reference model is the program itself: no second compiler is needed.
##
## Statements use R in locals, `seq[R]`, a `Pair` (lifted hooks), arrays,
## tuples, `ref Node`, strings, case objects, generic `W[R]`, inheritance +
## methods, closures, `move`, sinks, `lent`, `swap`, `if`/`case` expressions,
## raise/try/finally, break/continue/return. Reads are UB-free: moved vars are
## tracked (union over branches; loops and closures never move outer vars; a
## var touched in a statement is never also moved in it). Ref cycles are
## emitted only under `when defined(gcOrc)`.
##
## Each program is built 3 times with `-d:useLibc` (so valgrind sees the
## heap): `--mm:arc`, `--mm:orc`, and arc (even seed) or orc (odd seed) with
## `--opt:speed`, each run under valgrind. Signatures: `err:MSG:CFG`,
## `leak:CFG`, `crash:CFG:...`, `cfail:CFG:...`, `vg:KIND:CFG`, and
## `diff:arc-vs-orc` (modulo counts) / `diff:arc-vs-arcopt` (exact).
##
## The reducer keeps one proc, deletes statement chunks (halves .. single)
## and hoists compound bodies while one signature persists, rebuilding only
## the configs that signature names (valgrind only for `vg:`/`crash:`).
##
##   nim c -d:release -o:arc/arcfuzz arc/arcfuzz.nim
##   arc/arcfuzz --seed:1000 --count:20
##   arc/arcfuzz --seed:1004 --count:1 --sig:leak:orc   # reduce that signature

import std / [os, osproc, strutils, random, times, strformat, parseopt, sets, algorithm, tables]

const Prelude = """{.feature: "lenientnils".}
import std/[syncio, sequtils]

type
  R = object
    id: int
    v: int
  Pair = object
    a: R
    b: R
    s: string
  Node = ref object
    r: R
    next: Node
  Box = ref object
    cb: proc (): int {.closure.}
    r: R
  V = object
    case k: bool
    of true: r: R
    of false: s: seq[R]
  W[T] = object
    x: T
    y: seq[T]
  Base = ref object of RootObj
    r: R
  Der = ref object of Base
    r2: R

var gNext = 0
var gState: array[200000, int8]
var gErr = 0
var gCopies = 0
var gDups = 0
var gCreated = 0
var gDestroyed = 0
var gK: array[16, int] = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3]

proc err(msg: string; id: int) =
  inc gErr
  if gErr < 6: echo "ERR ", msg, " id=", id

proc fresh(): int =
  inc gNext
  inc gCreated
  if gNext < 200000: gState[gNext] = 1'i8
  result = gNext

proc `=destroy`(x: R) {.nodestroy.} =
  if x.id != 0:
    if x.id < 0 or x.id > gNext: err("destroy bad id", x.id)
    elif gState[x.id] != 1'i8: err("double destroy", x.id)
    else:
      gState[x.id] = 2'i8
      inc gDestroyed

proc `=wasMoved`(x: var R) {.nodestroy.} =
  x.id = 0
  x.v = 0

proc `=copy`(d: var R; s: R) {.nodestroy.} =
  if d.id == s.id: return
  `=destroy`(d)
  inc gCopies
  d.v = s.v
  if s.id == 0:
    d.id = 0
  else:
    if s.id < 0 or s.id > gNext or gState[s.id] != 1'i8: err("copy from dead", s.id)
    d.id = fresh()

proc `=dup`(s: R): R {.nodestroy.} =
  inc gDups
  result = R(id: 0, v: s.v)
  if s.id != 0:
    if s.id < 0 or s.id > gNext or gState[s.id] != 1'i8: err("dup from dead", s.id)
    result.id = fresh()

proc `=sink`(d: var R; s: R) {.nodestroy.} =
  `=destroy`(d)
  d.id = s.id
  d.v = s.v

proc mk(v: int): R = R(id: fresh(), v: v)

proc get(x: R): int =
  if x.id == 0: err("use of moved", 0)
  elif x.id < 0 or x.id > gNext or gState[x.id] != 1'i8: err("use of dead", x.id)
  result = x.v

proc rt(i: int): int = gK[i and 15]

proc takeSink(x: sink R): int = get(x)
proc eat(x: sink R; y: R): int = get(x) * 10 + get(y)
proc takeLent(x: var R): lent R = x
proc firstOf(p: var Pair): lent R = p.a
proc comb(a, b: R): R = mk(get(a) + get(b))
proc pass(x: sink R): R = x
proc keep(x: sink R; y: sink R): R =
  if get(x) > get(y): result = x
  else: result = y
proc mayRaise(x: R; k: int): R {.raises.} =
  if k > 6: raise ValueError
  result = mk(get(x) + 1)
proc sumSeq(s: seq[R]): int =
  result = 0
  for e in s: result = result + get(e)
proc sumSinkSeq(s: sink seq[R]): int =
  result = 0
  for e in s: result = result + get(e)
proc mkPair(a: sink R; s: string): Pair = Pair(a: a, b: mk(get(a) + 1), s: s)
proc ident[T](x: sink T): T = x
proc swapIt[T](a, b: var T) = swap(a, b)
proc mkEarly(k: int): R =
  result = mk(k)
  if k > 3: return
  result = mk(k + 1)
proc vval(v: V): int =
  if v.k: result = get(v.r)
  else: result = sumSeq(v.s)
proc wval(w: W[R]): int = get(w.x) + sumSeq(w.y)
method bval(b: Base): int {.base.} = get(b.r)
method bval(b: Der): int = get(b.r) * 100 + get(b.r2)

"""

const Epilogue = """
when defined(gcOrc): GC_fullCollect()
var leaks = 0
for i in 1..gNext:
  if gState[i] == 1'i8:
    inc leaks
    if leaks < 6: echo "LEAK id=", i
echo "SUMMARY created=", gCreated, " destroyed=", gDestroyed, " leaks=", leaks, " errs=", gErr, " copies=", gCopies, " dups=", gDups

{.feature: "assumeSync".}
"""

type
  Node = ref object             ## one generated statement
    line: string
    kids: seq[Node]                   ## body
    alts: seq[(string, seq[Node])]    ## `else:`, `of 0:`, `except:`, `finally:` ...
  Var = object                  ## a variable of the program being generated
    name: string
    kind: char  ## R S(seq) P(air) A(rray) T(uple) N(ode) s(tring) L(et R) C(ase obj) W B(ase)
    depth: int  ## loop depth of its declaration

# ---- generator state (one program at a time) ---------------------------------------

var
  rng: Rand
  counter, loopDepth, closureDepth, budget: int  ## budget: statements left in this proc
  scopes: seq[seq[Var]]
  moved: HashSet[string]    ## vars that may be moved-from here; never read
  touched: HashSet[string]  ## vars used in the current statement; never moved in it
  locked: HashSet[string]   ## seqs being iterated; no add/del/move

proc roll(): float = rng.rand(1.0)
proc randInt(a, b: int): int = rng.rand(a..b)
proc num(): int = randInt(0, 15)  ## index into the program's `gK` table
proc mkNum(): string = &"mk({num()})"
proc field(): string = rng.sample(["a", "b"])
proc newName(prefix: string): string = inc counter; prefix & $counter
let noKids: seq[Node] = @[]
proc node(line: string; kids: seq[Node] = @[]; alts: seq[(string, seq[Node])] = @[]): Node =
  Node(line: line, kids: kids, alts: alts)
proc echoed(what: string): Node = node("echo \"" & newName("e") & " \", " & what)
proc declare(name: string; k: char) = scopes[^1].add Var(name: name, kind: k, depth: loopDepth)
proc visible(k: char): seq[Var] =
  for sc in scopes:
    for v in sc:
      if v.kind == k: result.add v
proc live(k: char): seq[Var] =
  for v in visible(k):
    if v.name notin moved: result.add v
proc movable(k: char): seq[Var] =
  ## moving inside a loop or closure would move an outer var more than once
  for v in live(k):
    if v.name notin touched and v.depth == loopDepth and closureDepth == 0 and v.name notin locked:
      result.add v
proc without(vs: seq[Var]; name: string): seq[Var] =
  for v in vs:
    if v.name != name: result.add v
proc touch(vs: seq[Var]): string =
  ## a random var of `vs`, marked touched ("" if none)
  if vs.len == 0: return ""
  result = rng.sample(vs).name
  touched.incl result
proc pick(k: char): string = touch(live(k))  ## a readable var of kind `k`

# ---- expressions -----------------------------------------------------------------

# `d` is the nesting depth throughout; deeper means simpler choices.
proc rExpr(d = 0; canMove = true): string
proc rPure(d = 0): string = rExpr(d, false)  ## an R expression that moves nothing

proc cond(d = 0): string =
  ## a bool, mostly via `rt` so the compiler cannot fold it
  let x = roll()
  if x < 0.6 or d > 1: return &"rt({num()}) " & rng.sample([">", "<", "==", ">="]) & &" {randInt(1, 8)}"
  if x < 0.8: return &"get({rPure(d + 1)}) > {randInt(1, 20)}"
  let s = pick('S')
  if s != "": &"{s}.len > {randInt(0, 3)}" else: "true"

proc rPlace(): string =
  ## an lvalue of type R that can be read (not moved)
  var places: seq[(string, string)]  # (var, lvalue)
  for v in live('R') & live('L'): places.add (v.name, v.name)
  for v in live('P'): places.add (v.name, v.name & "." & field())
  for v in live('A'): places.add (v.name, &"{v.name}[{randInt(0, 2)}]")
  for v in live('T'): places.add (v.name, v.name & "[0]")
  for v in live('N') & live('B'): places.add (v.name, v.name & ".r")
  for v in live('W'): places.add (v.name, v.name & ".x")
  if places.len == 0: return ""
  let (name, place) = rng.sample(places)
  touched.incl name
  place

proc rExpr(d = 0; canMove = true): string =
  ## an expression of type R
  var x = roll()
  if d > 2: x *= 0.45  # deep: only leaves (mk, var reads, moves)
  template e: string = rExpr(d + 1, canMove)
  if x < 0.15: return mkNum()
  if x < 0.4:
    let s = rPlace()
    return if s != "": s else: mkNum()
  if x < 0.5 and canMove:
    let v = touch(movable('R'))
    if v == "": return mkNum()
    moved.incl v
    return &"move({v})"
  if x < 0.58: return &"pass({e})"
  if x < 0.66: return &"comb({e}, {e})"
  if x < 0.72: return &"keep({e}, {e})"
  if x < 0.8: return &"(if {cond(d + 1)}: {e} else: {e})"
  if x < 0.85: return &"(if {cond(d + 1)}: {e} elif {cond(d + 1)}: {e} else: {e})"
  if x < 0.9:
    var v = pick('R')
    if v != "": return &"takeLent({v})"
    v = pick('P')
    return if v != "": &"firstOf({v})" else: mkNum()
  if x < 0.95:
    let p = pick('P')
    return if p != "": &"mkPair({e}, \"q\").{field()}" else: mkNum()
  let t = pick('T')
  if t != "": t & "[0]" else: mkNum()

proc strExpr(): string =
  let s = pick('s')
  if s != "" and roll() < 0.5: return rng.sample([s, s & &" & \"{num()}\""])
  &"\"s{num()}\" & $rt({num()})"

proc seqExpr(): string =
  let x = roll()
  if x < 0.3: return "@[]"
  if x < 0.6:
    var a: seq[string]
    for _ in 1..randInt(1, 3): a.add rExpr(1)
    return "@[" & a.join(", ") & "]"
  if live('S').len > 0:
    if x < 0.8: return pick('S')
    let m = touch(movable('S'))   # a moved-from seq is empty, still readable
    if m != "": return &"move({m})"
  &"@[{rExpr(1)}]"

# ---- statements ------------------------------------------------------------------

proc stmt(d: int): Node

proc body(d: int; count = -1; scope = true): seq[Node] =
  let count = if count < 0: randInt(1, 4) else: count
  if scope: scopes.add @[]
  for _ in 0..<count: result.add stmt(d + 1)
  if scope: discard scopes.pop

proc branches(d, count: int): seq[seq[Node]] =
  ## alternative bodies: afterwards a var is moved if any branch moved it
  let before = moved
  var union = moved
  for _ in 0..<count:
    moved = before
    result.add body(d)
    union = union + moved
  moved = union

proc loop(d: int; head: string; pre: seq[Node] = @[]): Node =
  ## `head` with `pre` + a random body one loop level deeper
  let before = moved
  inc loopDepth
  let b = body(d)
  dec loopDepth
  moved = moved + before
  node(head, pre & b)

proc decl(k: char): Node =
  ## declares a new var of kind `k`
  var name, init: string
  case k
  of 'R':
    name = newName("x")
    if roll() < 0.15:
      result = node(&"var {name} = case rt({num()}) mod 3", @[],
                  @[("of 0: " & rExpr(1), noKids), ("of 1: " & rExpr(1), noKids), ("else: " & rExpr(1), noKids)])
    else: init = rExpr()
  of 'L': name = newName("l"); init = rExpr(canMove = roll() < 0.3)
  of 'S': name = newName("s") & ": seq[R]"; init = seqExpr()
  of 'P':
    name = newName("p")
    init = if roll() < 0.7: &"Pair(a: {rExpr()}, b: {rExpr()}, s: {strExpr()})" else: &"mkPair({rExpr()}, {strExpr()})"
  of 'A': name = newName("a"); init = &"[{rExpr(1)}, {rExpr(1)}, {rExpr(1)}]"
  of 'T': name = newName("t"); init = &"({rExpr()}, {num()})"
  of 'N': name = newName("n"); init = &"Node(r: {rExpr()})"
  of 's': name = newName("str"); init = strExpr()
  of 'C':
    name = newName("v")
    init = if roll() < 0.5: &"V(k: true, r: {rExpr()})" else: &"V(k: false, s: {seqExpr()})"
  of 'W': name = newName("wv"); init = &"W[R](x: {rExpr()}, y: {seqExpr()})"
  else:
    name = newName("bb") & ": Base"
    init = if roll() < 0.5: &"Der(r: {rExpr()}, r2: {rExpr()})" else: &"Base(r: {rExpr()})"
  if result == nil: result = node((if k == 'L': "let " else: "var ") & name & " = " & init)
  let colon = name.find(':')
  declare(if colon < 0: name else: name.substr(0, colon - 1), k)

proc setR(e: string; prob: float): Node =
  ## `t = e` for a visible, unmoved R (with chance `prob`); else `var x = e`
  let targets = visible('R')
  if targets.len > 0 and roll() < prob:
    let t = rng.sample(targets).name
    if t notin moved: return node(t & " = " & e)
  let name = newName("x")
  declare(name, 'R')
  node(&"var {name} = {e}")

proc assignOther(vs: seq[Var]; v: string): Node =
  ## `v = o` for another var of the same kind
  let o = touch(vs)
  node(&"{v} = {o}")

# Statement kinds and their weights; one-letter keys declare a var of that kind.
const Weights = {"R": 10, "assignR": 10, "useR": 10, "sinkcall": 5, "S": 4, "seqop": 9, "P": 3,
  "pairop": 5, "A": 2, "arrop": 3, "T": 2, "tupop": 3, "N": 3, "nodeop": 4, "s": 2, "strop": 2,
  "closure": 3, "destroyReset": 1, "raise": 2, "ret": 1, "mayRaise": 2, "L": 5, "C": 2, "vop": 4,
  "W": 2, "wop": 3, "B": 2, "bop": 3, "swap": 3, "selfAssign": 2, "early": 2, "identR": 2}
const Nested = {"if": 6, "while": 3, "for": 3, "case": 3, "try": 4, "block": 2}  # only while depth and budget allow

proc stmt(d: int): Node =
  touched.clear
  dec budget
  var weights = @Weights
  if d < 3 and budget > 0: weights.add @Nested
  if loopDepth > 0: weights.add [("brk", 2), ("cont", 2)]
  var total = 0
  for (_, w) in weights: total += w
  var left = roll() * float(total)
  var kind = ""
  for (n, w) in weights:
    kind = n
    left -= float(w)
    if left <= 0: break
  if kind.len == 1: return decl(kind[0])
  let x = roll()  # picks the variant within `kind`
  result = case kind
  of "assignR":
    let vs = visible('R')
    if x < 0.6 and vs.len > 0:
      let v = touch(vs)
      let e = rExpr()
      # an assignment revives the target only if declared in this scope
      var here = scopes.len == 1
      for d in scopes[^1]: here = here or d.name == v
      if here: moved.excl v
      return node(&"{v} = {e}")
    if x < 0.8:
      let p = pick('P')
      if p != "": return node(&"{p}.{field()} = {rExpr()}")
    let n = pick('N')
    if n != "": return node(&"{n}.r = {rExpr()}")
    decl('R')
  of "useR": echoed("get(" & rExpr(canMove = x < 0.5) & ")")
  of "sinkcall":
    if x < 0.4: return echoed(&"takeSink({rExpr()})")
    if x < 0.7:
      let v = pick('R')
      if v != "": return echoed(&"eat({v}, {v})")
    let s = pick('S')
    if s != "": return echoed(rng.sample(["sumSeq", "sumSinkSeq"]) & &"({s})")
    echoed(&"eat({rExpr()}, {rPure()})")
  of "seqop":
    var ss: seq[Var]
    for v in live('S'):
      if v.name notin locked: ss.add v
    let s = touch(ss)
    if s == "": return decl('S')
    if x < 0.25: return node(&"{s}.add {rExpr()}")
    if x < 0.33: return node(&"if {s}.len > 0: {s}.del(rt({num()}) mod {s}.len)")
    if x < 0.38: return node(&"if {s}.len > 1: {s}.setLen(1)")
    if x < 0.43: return node(&"{s}.insert([{rExpr()}], 0)")
    if x < 0.5:
      let targets = visible('R')
      if targets.len > 0 and roll() < 0.5:
        let t = rng.sample(targets).name
        if t notin moved: return node(&"if {s}.len > 0: {t} = {s}.pop")
      return node(&"if {s}.len > 0: discard {s}.pop")
    if x < 0.6:
      locked.incl s   # mutating a seq while iterating it is UB
      inc loopDepth
      let it = newName("it")
      result = node(&"for {it} in {s}:", @[echoed(&"get({it})")])
      if roll() < 0.5 and d < 3:
        scopes.add @[]
        let xn = newName("x")   # `it` is a borrowed R; copy it out
        result.kids.add node(&"var {xn} = {it}")
        declare(xn, 'R')
        result.kids.add body(d, randInt(0, 2), false)
        discard scopes.pop
      dec loopDepth
      locked.excl s
      return
    if x < 0.7:
      let k = randInt(0, 2)
      let t = if roll() < 0.6: touch(live('R')) else: ""
      if t != "": return node(&"if {s}.len > {k}: {t} = {s}[{k}]")
      return node(&"if {s}.len > {k}: {s}[{k}] = {rExpr()}")
    if x < 0.78:
      let i = newName("i")
      inc loopDepth   # `e` runs once per iteration
      locked.incl s
      let e = rExpr()
      locked.excl s
      dec loopDepth
      return node(&"for {i} in 0..<{s}.len: {s}[{i}] = {e}")
    if x < 0.85: return node(&"{s} = {seqExpr()}")
    if x < 0.92: return echoed(&"{s}.len")
    let k = randInt(0, 2)
    let t = touch(movable('R'))
    if t == "": return echoed(&"sumSeq({s})")
    # move out of a seq slot, refill it
    node(&"if {s}.len > {k}:", @[node(&"{t} = move({s}[{k}])"), node(&"{s}[{k}] = {rPure()}")])
  of "pairop":
    let ps = live('P')
    let p = touch(ps)
    if p == "": return decl('P')
    if x < 0.3: return node(&"{p}.{field()} = {rExpr()}")
    if x < 0.45: return echoed(&"get({p}.a), \" \", get({p}.b), \" \", {p}.s")
    if x < 0.55: return node(&"{p}.s = {p}.s & {strExpr()}")
    if x < 0.7:
      let o = ps.without(p)
      if o.len > 0: return assignOther(o, p)
      return node(&"{p} = Pair(a: {rExpr()}, b: {p}.a, s: \"z\")")
    if x < 0.8:
      let t = touch(movable('R'))
      if t != "":
        let f = field()
        return node("block:", @[node(&"{t} = move({p}.{f})"), node(&"{p}.{f} = {mkNum()}")])
    if x < 0.9:
      let a = newName("x")
      let b = newName("x")
      declare(a, 'R')
      declare(b, 'R')
      return node(&"var ({a}, {b}) = ({p}.a, {p}.b)")
    echoed(&"get(firstOf({p}))")
  of "arrop":
    let aa = live('A')
    let a = touch(aa)
    if a == "": return decl('A')
    if x < 0.35: return node(&"{a}[{randInt(0, 2)}] = {rExpr()}")
    if x < 0.5: return node(&"{a}[rt({num()}) mod 3] = {rExpr()}")
    if x < 0.65: return echoed(&"get({a}[0]) + get({a}[1]) + get({a}[2])")
    let o = aa.without(a)
    if x < 0.8 and o.len > 0: return assignOther(o, a)
    let it = newName("it")
    node(&"for {it} in {a}: echo get({it})")
  of "tupop":
    let t = pick('T')
    if t == "": return decl('T')
    if x < 0.35: return node(&"{t}[0] = {rExpr()}")
    if x < 0.6:
      let xn = newName("x")
      let k = newName("k")
      declare(xn, 'R')
      return node(&"var ({xn}, {k}) = {t}")
    if x < 0.8: return echoed(&"get({t}[0]) + {t}[1]")
    node(&"{t} = ({rExpr()}, {t}[1] + 1)")
  of "nodeop":
    let ns = live('N')
    let n = touch(ns)
    if n == "": return decl('N')
    if x < 0.3: return node(&"when defined(gcOrc): {n}.next = " & rng.sample(ns).name)  # cycles: ORC only
    if x < 0.5: return node(&"{n}.r = {rExpr()}")
    if x < 0.65: return echoed(&"get({n}.r)")
    if x < 0.8: return assignOther(ns, n)
    if x < 0.9:
      let b = newName("b")   # a cycle through a closure env (ORC only)
      return node("when defined(gcOrc):", @[node(&"var {b} = Box(r: {rPure()})"),
        node(&"{b}.cb = proc (): int {{.closure.}} = get({b}.r) + get({n}.r) + (if {b}.cb != nil: 1 else: 0)"),
        node(&"discard {b}.cb()")])
    node(&"{n} = Node(r: {rExpr()}, next: nil)")
  of "strop":
    let s = pick('s')
    if s == "": return decl('s')
    if x < 0.5: node(s & ".add \"x\"") else: echoed(s)
  of "closure":
    let c = newName("c")
    inc closureDepth
    let n = if x < 0.5:
        node("block:", @[node(&"let {c} = proc (): int {{.closure.}} = get({rPure(1)}) + get({rPure(1)})"), echoed(c & "()")])
      elif x < 0.75:
        let v = pick('R')
        if v == "": echoed("0") else: node("block:", @[node(&"let {c} = proc () {{.closure.}} = {v} = {rPure(1)}"),
                                                 node(c & "()"), echoed(&"get({v})")])
      else:
        let z = newName("x")
        node("block:", @[node(&"var {z} = {rPure(1)}"),
          node(&"let {c} = proc (k: int): R {{.closure.}} = comb({z}, mk(k))"), echoed(&"get({c}({num()}))")])
    dec closureDepth
    n
  of "destroyReset":
    let v = touch(movable('R'))
    if v == "": return decl('R')
    moved.incl v
    node(&"`=destroy`({v}); `=wasMoved`({v})")
  of "raise": node(&"if rt({num()}) > {randInt(5, 9)}: raise ValueError")
  of "ret": node(&"if rt({num()}) > {randInt(6, 9)}: return")
  of "brk": node(&"if rt({num()}) > {randInt(3, 8)}: break")
  of "cont": node(&"if rt({num()}) > {randInt(3, 8)}: continue")
  of "mayRaise": setR(&"mayRaise({rPure()}, rt({num()}))", 0.6)
  of "early": setR(&"mkEarly(rt({num()}))", 0.5)
  of "vop":
    let vs = live('C')
    let v = touch(vs)
    if v == "": return decl('C')
    if x < 0.3: return echoed(&"vval({v})")
    if x < 0.5: return node(&"{v} = V(k: true, r: {rExpr()})")
    if x < 0.65: return node(&"{v} = V(k: false, s: {seqExpr()})")
    if x < 0.8: return node(&"if {v}.k: {v}.r = {rPure()}")
    assignOther(vs, v)
  of "wop":
    let ws = live('W')
    let v = touch(ws)
    if v == "": return decl('W')
    if x < 0.3: return echoed(&"wval({v})")
    if x < 0.5: return node(&"{v}.x = {rExpr()}")
    if x < 0.65: return node(&"{v}.y.add {rExpr()}")
    if x < 0.8: return node(&"if {v}.y.len > 0: {v}.x = {v}.y[0]")
    assignOther(ws, v)
  of "bop":
    let bs = live('B')
    let v = touch(bs)
    if v == "": return decl('B')
    if x < 0.4: return echoed(&"bval({v})")
    if x < 0.6: return node(&"{v}.r = {rExpr()}")
    if x < 0.8: return node(&"{v} = Der(r: {rExpr()}, r2: {v}.r)")
    assignOther(bs, v)
  of "swap":
    var vs = live('R')
    if vs.len < 2: return decl('R')
    rng.shuffle(vs)
    node((if x < 0.5: "swap(" else: "swapIt(") & vs[0].name & ", " & vs[1].name & ")")
  of "selfAssign":
    let v = pick('R')
    if v == "": return decl('R')
    if x < 0.5: return node(&"{v} = {v}")
    let p = pick('P')
    if p != "": node(&"{p}.a = {p}.a") else: node(&"{v} = comb({v}, {v})")
  of "identR":
    if x < 0.5: return echoed(&"get(ident({rExpr()}))")
    let s = pick('S')
    if s != "": echoed(&"sumSeq(ident({s}))") else: echoed(&"get(ident({mkNum()}))")
  of "if":
    let c = cond()
    if x < 0.6:
      let b = branches(d, 2)
      node(&"if {c}:", b[0], @[("else:", b[1])])
    else: node(&"if {c}:", branches(d, 1)[0])
  of "case":
    let b = branches(d, 3)
    node(&"case rt({num()}) mod 3", @[], @[("of 0:", b[0]), ("of 1:", b[1]), ("else:", b[2])])
  of "while":
    let i = newName("w")
    node("block:", @[node(&"var {i} = 0"), loop(d, &"while {i} < rt({num()}) mod 4:", @[node(&"inc {i}")])])
  of "for":
    let j = newName("j")
    loop(d, &"for {j} in 0..<{randInt(1, 3)}:")
  of "try":
    let before = moved
    let b = body(d)
    moved = before + moved   # `except:` may run after any prefix of the body
    var alts = @[("except:", @[echoed("\"caught\"")] & body(d, randInt(0, 2)))]
    if roll() < 0.3: alts.add ("finally:", body(d, randInt(1, 2)))
    node("try:", b, alts)
  else: node("block:", body(d))

proc generate(seed: int): seq[seq[Node]] =
  ## the bodies of procs `t0`, `t1`, ...
  rng = initRand(seed)
  counter = 0
  for _ in 0..<randInt(4, 7):
    scopes = @[newSeq[Var]()]
    moved.clear; locked.clear
    loopDepth = 0; closureDepth = 0
    budget = randInt(15, 35)
    var b: seq[Node]
    while budget > 0: b.add stmt(0)
    result.add b

# ---- rendering -------------------------------------------------------------------

var prog: seq[seq[Node]]  ## current program: proc bodies, shrunk in place by the reducer
var only = -1   ## render only proc `t<only>` (reducer)

proc render(n: Node; indent: int; res: var string) =
  let pad = repeat("  ", indent)
  res.add pad & n.line & "\n"
  for k in n.kids: render(k, indent + 1, res)
  # the reducer may empty a body
  if n.line.endsWith(":") and n.kids.len == 0: res.add pad & "  discard\n"
  for (head, ks) in n.alts:
    res.add pad & head & "\n"
    for k in ks: render(k, indent + 1, res)
    if ks.len == 0 and head.endsWith(":"): res.add pad & "  discard\n"

proc render(): string =
  ## the full program source
  result = Prelude
  var main = "proc main() =\n"
  for i, b in prog:
    if only >= 0 and i != only: continue
    result.add &"proc t{i}() {{.raises.}} =\n"
    if b.len == 0: result.add "  discard\n"
    for n in b: render(n, 1, result)
    result.add "\n"
    main.add &"  try: t{i}()\n  except: echo \"exc t{i}\"\n"
  result.add main & "main()\n" & Epilogue

# ---- oracle ----------------------------------------------------------------------

var nimony = "/home/ageralis/Projects/nimony/bin/nimony"
var work = ""
const Valgrind = "valgrind -q --leak-check=full --errors-for-leak-kinds=definite --show-leak-kinds=definite --error-exitcode=99 "
const VgErrors = {"Invalid read": "invalid-read", "Invalid write": "invalid-write", "Invalid free": "invalid-free",
  "definitely lost": "def-lost", "uninitialised": "uninit", "Mismatched free": "mismatched-free"}

proc normErr(s: string): string =
  ## the identifying line of an error, numbers replaced by N
  var l = ""
  for x in s.splitLines:
    if not x.isEmptyOrWhitespace: l = x
  for x in s.splitLines:
    if "Error:" in x or "BUG" in x or "Assertion" in x or "SIGSEGV" in x or "Defect" in x:
      let e = x.rfind("Error:")
      l = if e < 0: x else: x.substr(e + "Error:".len)
      break
  for c in l.strip:
    if c notin Digits: result.add c
    elif not result.endsWith('N'): result.add 'N'
  result.setLen min(result.len, 120)

proc noCounts(o: string): string =
  ## created/destroyed/copies/dups legitimately differ when `when defined(gcOrc)` code runs
  for l in o.splitLines:
    if l.startsWith("SUMMARY"):
      var sep = ""
      for f in l.split:
        if f.startsWith("leaks=") or f.startsWith("errs="):
          result.add sep & f
          sep = " "
    else: result.add l
    result.add '\n'

proc check(src: string; cfgs: seq[string]; valgrind = true): (seq[string], string) =
  ## build + run `src` under each config: (signatures, details)
  var sigs: seq[string]
  var details = ""
  var outs: Table[string, string]  ## stdout per config
  template hit(x: string) =
    let y = x
    if y notin sigs: sigs.add y
  writeFile(work / "fz.nim", src)
  for cfg in cfgs:
    let dir = work / cfg
    let exe = dir / "fz"
    let cmd = nimony & " c " & (if cfg.startsWith("arc"): "--mm:arc" else: "--mm:orc") &
              (if cfg.endsWith("opt"): " --opt:speed" else: "") & " -d:useLibc --nimcache:" & dir &
              " -o:" & exe & " " & work / "fz.nim"
    removeDir dir
    var (o, rc) = execCmdEx(cmd)
    if rc != 0 and "deps.nif" in o:   # known flake, re-run once
      removeDir dir
      (o, rc) = execCmdEx(cmd)
    if rc != 0 or not fileExists(exe):
      hit &"cfail:{cfg}:{normErr(o)}"
      details.add &"===== {cfg}\n{o.substr(o.len - 3000)}\n"
      continue
    let (output, code) = execCmdEx("timeout 120 " & (if valgrind: Valgrind else: "") & exe & " 2>" & dir / "stderr.txt")
    let errs = readFile(dir / "stderr.txt")
    outs[cfg] = output
    details.add &"===== {cfg} rc={code}\n--- stdout tail\n{output.substr(output.len - 1500)}\n--- stderr tail\n{errs.substr(errs.len - 3000)}\n"
    for l in output.splitLines:
      let id = l.find(" id=")
      if l.startsWith("ERR ") and id >= 0: hit "err:" & l.substr(4, id - 1) & ":" & cfg
      if l.startsWith("LEAK"): hit &"leak:{cfg}"
    if "SUMMARY" notin output: hit &"crash:{cfg}:rc={code}:{normErr(errs)}"
    for (pat, k) in VgErrors:
      if pat in errs: hit &"vg:{k}:{cfg}"
  if "arc" in outs and "orc" in outs and noCounts(outs["arc"]) != noCounts(outs["orc"]): hit "diff:arc-vs-orc"
  for b in ["arc", "orc"]:
    if b in outs and b & "opt" in outs and outs[b] != outs[b & "opt"]: hit &"diff:{b}-vs-{b}opt"
  (sigs.sorted, details)

# ---- reducer ---------------------------------------------------------------------

var target = ""      ## the signature being reduced
var tests = 0
var maxTests = 150   ## `--budget`

proc cfgsOf(sig: string): seq[string] =
  ## the configs a signature needs rebuilt
  let p = sig.split(':')
  case p[0]
  of "diff": p[1].split("-vs-")
  of "err": @[p[^1]]
  of "vg": @[p[2]]
  else: @[p[1]]

proc stillHits(): bool =
  ## does the current program still show `target`? (valgrind only when it matters)
  inc tests
  if tests > maxTests: return false
  result = target in check(render(), cfgsOf(target), target.startsWith("vg:") or target.startsWith("crash:"))[0]
  if result: echo &"  test {tests}: hit, {render().countLines} lines"

proc shrink(stmts: var seq[Node]): bool =
  ## delete chunks (halves .. single), then hoist or recurse into compound statements
  var chunk = max(1, stmts.len div 2)
  while true:
    var i = 0
    while i < stmts.len:
      let j = min(i + chunk, stmts.len)
      let saved = stmts[i ..< j]
      for _ in i ..< j: stmts.delete(i)
      if stillHits(): result = true
      else:
        for k, s in saved: stmts.insert(s, i + k)
        i = j
    if chunk == 1: break
    chunk = chunk div 2
  var i = 0
  while i < stmts.len:
    let n = stmts[i]
    var hoisted = false
    if n.kids.len + n.alts.len > 0:
      var bodies = @[n.kids]
      for (_, ks) in n.alts:
        if ks.len > 0: bodies.add ks
      for b in bodies:   # replace the statement by one of its bodies
        stmts.delete(i)
        for k, s in b: stmts.insert(s, i + k)
        if stillHits():
          hoisted = true
          break
        for _ in 0 ..< b.len: stmts.delete(i)
        stmts.insert(n, i)
    if hoisted: result = true
    else:
      if shrink(n.kids): result = true
      for a in n.alts.mitems:
        if shrink(a[1]): result = true
      inc i

proc reduce(): string =
  ## shrinks `prog` while `target` persists; returns the reduced source
  tests = 0
  # first try each proc alone
  for i in 0..<prog.len:
    only = i
    if stillHits(): break
    only = -1
  var changed = true
  while changed and tests <= maxTests:
    changed = false
    for i in 0..<prog.len:
      if (only < 0 or i == only) and shrink(prog[i]): changed = true
  render()

# ---- driver ----------------------------------------------------------------------

proc main() =
  var seed = int(epochTime() * 1000) mod 1_000_000
  var count = 10
  var outDir = getAppDir() / "out"
  var doReduce = true
  var wantSig = ""
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": work = val
    of "budget": maxTests = parseInt(val)
    of "sig": wantSig = val
    of "noreduce": doReduce = false
    else: quit "unknown option: " & key
  if work == "": work = getAppDir() / "work" / ("s" & $seed)  # one per process
  nimony = absolutePath(nimony)
  work = absolutePath(work)
  outDir = absolutePath(outDir)
  createDir work
  createDir outDir
  let start = epochTime()
  var found = 0
  for k in 0..<count:
    let progSeed = seed + k
    prog = generate(progSeed)
    only = -1
    let started = epochTime()
    let (sig, details) = check(render(), @["arc", "orc", (if progSeed mod 2 == 0: "arcopt" else: "orcopt")])
    let elapsed = int(epochTime() - start)
    if sig.len == 0:
      echo &"[{elapsed}s] seed {progSeed}: ok ({int(epochTime() - started)}s)"
      continue
    inc found
    echo &"[{elapsed}s] seed {progSeed}: " & sig.join(" ")
    let dir = outDir / &"s{progSeed}"
    createDir dir
    writeFile(dir / "prog.nim", render())
    writeFile(dir / "details.txt", sig.join("\n") & "\n\n" & details)
    let f = open(outDir / "log.csv", fmAppend)
    f.writeLine(&"{elapsed},{k + 1},{progSeed},\"" & sig.join("+") & "\"")
    f.close
    if not doReduce: continue
    target = wantSig
    if target notin sig:   # else the most severe signature
      target = ""
      for p in ["err:", "vg:", "crash:", "cfail:", "leak:", "diff:"]:
        for x in sig:
          if target == "" and x.startsWith(p): target = x
    echo &"  reducing {target}"
    let reduced = reduce()
    writeFile(dir / "reduced.nim", reduced)
    echo &"  reduced to {reduced.countLines} lines in {tests} tests: {dir}/reduced.nim"
  echo &"{count} programs, {found} with findings, {int(epochTime() - start)}s -> {outDir}"
  if found > 0: quit 1

main()
