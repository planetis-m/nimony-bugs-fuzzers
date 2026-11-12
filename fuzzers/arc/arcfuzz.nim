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

import std / [os, osproc, strutils, random, times, strformat, parseopt, sets, sequtils, algorithm, tables]

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
  Node = ref object
    line: string
    kids: seq[Node]                   ## body
    alts: seq[(string, seq[Node])]    ## `else:`, `of 0:`, `except:`, `finally:` ...
  Var = object
    name: string
    kind: char  ## R S(seq) P(air) A(rray) T(uple) N(ode) s(tring) L(et R) C(ase obj) W B(ase)
    loop: int

# ---- generator state (one program at a time) ---------------------------------------

var
  r: Rand
  cnt, loopD, closD, budget: int
  scopes: seq[seq[Var]]
  moved, touched, locked: HashSet[string]

proc rf(): float = r.rand(1.0)
proc ri(a, b: int): int = r.rand(a..b)
proc K(): int = ri(0, 15)
proc mkK(): string = &"mk({K()})"
proc ab(): string = r.sample(["a", "b"])
proc fresh(p: string): string = inc cnt; p & $cnt
let none: seq[Node] = @[]
proc st(line: string; kids: seq[Node] = @[]; alts: seq[(string, seq[Node])] = @[]): Node =
  Node(line: line, kids: kids, alts: alts)
proc ec(what: string): Node = st("echo \"" & fresh("e") & " \", " & what)
proc declare(n: string; k: char) = scopes[^1].add Var(name: n, kind: k, loop: loopD)
proc visible(k: char): seq[Var] =
  for sc in scopes:
    for v in sc:
      if v.kind == k: result.add v
proc live(k: char): seq[Var] = visible(k).filterIt(it.name notin moved)
proc movable(k: char): seq[Var] =
  live(k).filterIt(it.name notin touched and it.loop == loopD and closD == 0 and it.name notin locked)
proc touch(vs: seq[Var]): string =
  ## a random var of `vs`, marked touched ("" if none)
  if vs.len == 0: return ""
  result = r.sample(vs).name
  touched.incl result
proc pk(k: char): string = touch(live(k))

# ---- expressions -----------------------------------------------------------------

proc rexpr(d = 0; mv = true): string
proc rn(d = 0): string = rexpr(d, false)

proc cond(d = 0): string =
  let x = rf()
  if x < 0.6 or d > 1: return &"rt({K()}) " & r.sample([">", "<", "==", ">="]) & &" {ri(1, 8)}"
  if x < 0.8: return &"get({rn(d + 1)}) > {ri(1, 20)}"
  let s = pk('S')
  if s != "": &"{s}.len > {ri(0, 3)}" else: "true"

proc rvarRead(): string =
  ## an lvalue of type R that can be read (not moved)
  var o: seq[(string, string)]
  for v in live('R') & live('L'): o.add (v.name, v.name)
  for v in live('P'): o.add (v.name, v.name & "." & ab())
  for v in live('A'): o.add (v.name, &"{v.name}[{ri(0, 2)}]")
  for v in live('T'): o.add (v.name, v.name & "[0]")
  for v in live('N') & live('B'): o.add (v.name, v.name & ".r")
  for v in live('W'): o.add (v.name, v.name & ".x")
  if o.len == 0: return ""
  let (n, s) = r.sample(o)
  touched.incl n
  s

proc rexpr(d = 0; mv = true): string =
  var x = rf()
  if d > 2: x *= 0.45
  template e: string = rexpr(d + 1, mv)
  if x < 0.15: return mkK()
  if x < 0.4:
    let s = rvarRead()
    return if s != "": s else: mkK()
  if x < 0.5 and mv:
    let v = touch(movable('R'))
    if v == "": return mkK()
    moved.incl v
    return &"move({v})"
  if x < 0.58: return &"pass({e})"
  if x < 0.66: return &"comb({e}, {e})"
  if x < 0.72: return &"keep({e}, {e})"
  if x < 0.8: return &"(if {cond(d + 1)}: {e} else: {e})"
  if x < 0.85: return &"(if {cond(d + 1)}: {e} elif {cond(d + 1)}: {e} else: {e})"
  if x < 0.9:
    var v = pk('R')
    if v != "": return &"takeLent({v})"
    v = pk('P')
    return if v != "": &"firstOf({v})" else: mkK()
  if x < 0.95:
    let p = pk('P')
    return if p != "": &"mkPair({e}, \"q\").{ab()}" else: mkK()
  let t = pk('T')
  if t != "": t & "[0]" else: mkK()

proc strexpr(): string =
  let s = pk('s')
  if s != "" and rf() < 0.5: return r.sample([s, s & &" & \"{K()}\""])
  &"\"s{K()}\" & $rt({K()})"

proc seqexpr(): string =
  let x = rf()
  if x < 0.3: return "@[]"
  if x < 0.6:
    var a: seq[string]
    for _ in 1..ri(1, 3): a.add rexpr(1)
    return "@[" & a.join(", ") & "]"
  if live('S').len > 0:
    if x < 0.8: return pk('S')
    let m = touch(movable('S'))   # a moved-from seq is empty, still readable
    if m != "": return &"move({m})"
  &"@[{rexpr(1)}]"

# ---- statements ------------------------------------------------------------------

proc stmt(d: int): Node

proc body(d: int; n = -1; scope = true): seq[Node] =
  let n = if n < 0: ri(1, 4) else: n
  if scope: scopes.add @[]
  for _ in 0..<n: result.add stmt(d + 1)
  if scope: discard scopes.pop

proc branchy(d, k: int): seq[seq[Node]] =
  ## alternative bodies: afterwards a var is moved if any branch moved it
  let before = moved
  var u = moved
  for _ in 0..<k:
    moved = before
    result.add body(d)
    u = u + moved
  moved = u

proc loop(d: int; head: string; pre: seq[Node] = @[]): Node =
  let before = moved
  inc loopD
  let b = body(d)
  dec loopD
  moved = moved + before
  st(head, pre & b)

proc decl(k: char): Node =
  var n, e: string
  case k
  of 'R':
    n = fresh("x")
    if rf() < 0.15:
      result = st(&"var {n} = case rt({K()}) mod 3", @[],
                  @[("of 0: " & rexpr(1), none), ("of 1: " & rexpr(1), none), ("else: " & rexpr(1), none)])
    else: e = rexpr()
  of 'L': n = fresh("l"); e = rexpr(mv = rf() < 0.3)
  of 'S': n = fresh("s") & ": seq[R]"; e = seqexpr()
  of 'P':
    n = fresh("p")
    e = if rf() < 0.7: &"Pair(a: {rexpr()}, b: {rexpr()}, s: {strexpr()})" else: &"mkPair({rexpr()}, {strexpr()})"
  of 'A': n = fresh("a"); e = &"[{rexpr(1)}, {rexpr(1)}, {rexpr(1)}]"
  of 'T': n = fresh("t"); e = &"({rexpr()}, {K()})"
  of 'N': n = fresh("n"); e = &"Node(r: {rexpr()})"
  of 's': n = fresh("str"); e = strexpr()
  of 'C':
    n = fresh("v")
    e = if rf() < 0.5: &"V(k: true, r: {rexpr()})" else: &"V(k: false, s: {seqexpr()})"
  of 'W': n = fresh("wv"); e = &"W[R](x: {rexpr()}, y: {seqexpr()})"
  else:
    n = fresh("bb") & ": Base"
    e = if rf() < 0.5: &"Der(r: {rexpr()}, r2: {rexpr()})" else: &"Base(r: {rexpr()})"
  if result == nil: result = st((if k == 'L': "let " else: "var ") & n & " = " & e)
  declare(n.split(':')[0], k)

proc setR(e: string; p: float): Node =
  ## `t = e` for a visible, unmoved R; else `var x = e`
  let tg = visible('R')
  if tg.len > 0 and rf() < p:
    let t = r.sample(tg).name
    if t notin moved: return st(t & " = " & e)
  let n = fresh("x")
  declare(n, 'R')
  st(&"var {n} = {e}")

proc other(vs: seq[Var]; v: string): Node =
  ## `v = o` for another var of the same kind
  let o = touch(vs)
  st(&"{v} = {o}")

const Weights = {"R": 10, "assignR": 10, "useR": 10, "sinkcall": 5, "S": 4, "seqop": 9, "P": 3,
  "pairop": 5, "A": 2, "arrop": 3, "T": 2, "tupop": 3, "N": 3, "nodeop": 4, "s": 2, "strop": 2,
  "closure": 3, "destroyReset": 1, "raise": 2, "ret": 1, "mayRaise": 2, "L": 5, "C": 2, "vop": 4,
  "W": 2, "wop": 3, "B": 2, "bop": 3, "swap": 3, "selfAssign": 2, "early": 2, "identR": 2}
const Nested = {"if": 6, "while": 3, "for": 3, "case": 3, "try": 4, "block": 2}

proc stmt(d: int): Node =
  touched.clear
  dec budget
  var w = @Weights
  if d < 3 and budget > 0: w.add @Nested
  if loopD > 0: w.add [("brk", 2), ("cont", 2)]
  var p = rf() * float(w.mapIt(it[1]).foldl(a + b))
  var what = ""
  for (n, k) in w:
    what = n
    p -= float(k)
    if p <= 0: break
  if what.len == 1: return decl(what[0])
  let x = rf()
  result = case what
  of "assignR":
    let vs = visible('R')
    if x < 0.6 and vs.len > 0:
      let v = r.sample(vs).name
      touched.incl v
      let e = rexpr()
      # an assignment revives the target only if declared in this scope
      if scopes.len == 1 or scopes[^1].anyIt(it.name == v): moved.excl v
      return st(&"{v} = {e}")
    if x < 0.8:
      let p = pk('P')
      if p != "": return st(&"{p}.{ab()} = {rexpr()}")
    let n = pk('N')
    if n != "": return st(&"{n}.r = {rexpr()}")
    decl('R')
  of "useR": ec("get(" & rexpr(mv = x < 0.5) & ")")
  of "sinkcall":
    if x < 0.4: return ec(&"takeSink({rexpr()})")
    if x < 0.7:
      let v = pk('R')
      if v != "": return ec(&"eat({v}, {v})")
    let s = pk('S')
    if s != "": return ec(r.sample(["sumSeq", "sumSinkSeq"]) & &"({s})")
    ec(&"eat({rexpr()}, {rn()})")
  of "seqop":
    let s = touch(live('S').filterIt(it.name notin locked))
    if s == "": return decl('S')
    if x < 0.25: return st(&"{s}.add {rexpr()}")
    if x < 0.33: return st(&"if {s}.len > 0: {s}.del(rt({K()}) mod {s}.len)")
    if x < 0.38: return st(&"if {s}.len > 1: {s}.setLen(1)")
    if x < 0.43: return st(&"{s}.insert([{rexpr()}], 0)")
    if x < 0.5:
      let tg = visible('R')
      if tg.len > 0 and rf() < 0.5:
        let t = r.sample(tg).name
        if t notin moved: return st(&"if {s}.len > 0: {t} = {s}.pop")
      return st(&"if {s}.len > 0: discard {s}.pop")
    if x < 0.6:
      locked.incl s
      inc loopD
      let it = fresh("it")
      result = st(&"for {it} in {s}:", @[ec(&"get({it})")])
      if rf() < 0.5 and d < 3:
        scopes.add @[]
        let xn = fresh("x")   # `it` is a borrowed R; copy it out
        result.kids.add st(&"var {xn} = {it}")
        declare(xn, 'R')
        result.kids.add body(d, ri(0, 2), false)
        discard scopes.pop
      dec loopD
      locked.excl s
      return
    if x < 0.7:
      let k = ri(0, 2)
      let t = if rf() < 0.6: touch(live('R')) else: ""
      if t != "": return st(&"if {s}.len > {k}: {t} = {s}[{k}]")
      return st(&"if {s}.len > {k}: {s}[{k}] = {rexpr()}")
    if x < 0.78:
      let i = fresh("i")
      inc loopD
      locked.incl s
      let e = rexpr()
      locked.excl s
      dec loopD
      return st(&"for {i} in 0..<{s}.len: {s}[{i}] = {e}")
    if x < 0.85: return st(&"{s} = {seqexpr()}")
    if x < 0.92: return ec(&"{s}.len")
    let k = ri(0, 2)
    let t = touch(movable('R'))
    if t == "": return ec(&"sumSeq({s})")
    # move out of a seq slot, refill it
    st(&"if {s}.len > {k}:", @[st(&"{t} = move({s}[{k}])"), st(&"{s}[{k}] = {rn()}")])
  of "pairop":
    let ps = live('P')
    let p = touch(ps)
    if p == "": return decl('P')
    if x < 0.3: return st(&"{p}.{ab()} = {rexpr()}")
    if x < 0.45: return ec(&"get({p}.a), \" \", get({p}.b), \" \", {p}.s")
    if x < 0.55: return st(&"{p}.s = {p}.s & {strexpr()}")
    if x < 0.7:
      let o = ps.filterIt(it.name != p)
      if o.len > 0: return other(o, p)
      return st(&"{p} = Pair(a: {rexpr()}, b: {p}.a, s: \"z\")")
    if x < 0.8:
      let t = touch(movable('R'))
      if t != "":
        let f = ab()
        return st("block:", @[st(&"{t} = move({p}.{f})"), st(&"{p}.{f} = {mkK()}")])
    if x < 0.9:
      let a = fresh("x")
      let b = fresh("x")
      declare(a, 'R')
      declare(b, 'R')
      return st(&"var ({a}, {b}) = ({p}.a, {p}.b)")
    ec(&"get(firstOf({p}))")
  of "arrop":
    let aa = live('A')
    let a = touch(aa)
    if a == "": return decl('A')
    if x < 0.35: return st(&"{a}[{ri(0, 2)}] = {rexpr()}")
    if x < 0.5: return st(&"{a}[rt({K()}) mod 3] = {rexpr()}")
    if x < 0.65: return ec(&"get({a}[0]) + get({a}[1]) + get({a}[2])")
    let o = aa.filterIt(it.name != a)
    if x < 0.8 and o.len > 0: return other(o, a)
    let it = fresh("it")
    st(&"for {it} in {a}: echo get({it})")
  of "tupop":
    let t = pk('T')
    if t == "": return decl('T')
    if x < 0.35: return st(&"{t}[0] = {rexpr()}")
    if x < 0.6:
      let xn = fresh("x")
      let k = fresh("k")
      declare(xn, 'R')
      return st(&"var ({xn}, {k}) = {t}")
    if x < 0.8: return ec(&"get({t}[0]) + {t}[1]")
    st(&"{t} = ({rexpr()}, {t}[1] + 1)")
  of "nodeop":
    let ns = live('N')
    let n = touch(ns)
    if n == "": return decl('N')
    if x < 0.3: return st(&"when defined(gcOrc): {n}.next = " & r.sample(ns).name)  # cycles: ORC only
    if x < 0.5: return st(&"{n}.r = {rexpr()}")
    if x < 0.65: return ec(&"get({n}.r)")
    if x < 0.8: return other(ns, n)
    if x < 0.9:
      let b = fresh("b")   # a cycle through a closure env (ORC only)
      return st("when defined(gcOrc):", @[st(&"var {b} = Box(r: {rn()})"),
        st(&"{b}.cb = proc (): int {{.closure.}} = get({b}.r) + get({n}.r) + (if {b}.cb != nil: 1 else: 0)"),
        st(&"discard {b}.cb()")])
    st(&"{n} = Node(r: {rexpr()}, next: nil)")
  of "strop":
    let s = pk('s')
    if s == "": return decl('s')
    if x < 0.5: st(s & ".add \"x\"") else: ec(s)
  of "closure":
    let c = fresh("c")
    inc closD
    let n = if x < 0.5:
        st("block:", @[st(&"let {c} = proc (): int {{.closure.}} = get({rn(1)}) + get({rn(1)})"), ec(c & "()")])
      elif x < 0.75:
        let v = pk('R')
        if v == "": ec("0") else: st("block:", @[st(&"let {c} = proc () {{.closure.}} = {v} = {rn(1)}"),
                                                 st(c & "()"), ec(&"get({v})")])
      else:
        let z = fresh("x")
        st("block:", @[st(&"var {z} = {rn(1)}"),
          st(&"let {c} = proc (k: int): R {{.closure.}} = comb({z}, mk(k))"), ec(&"get({c}({K()}))")])
    dec closD
    n
  of "destroyReset":
    let v = touch(movable('R'))
    if v == "": return decl('R')
    moved.incl v
    st(&"`=destroy`({v}); `=wasMoved`({v})")
  of "raise": st(&"if rt({K()}) > {ri(5, 9)}: raise ValueError")
  of "ret": st(&"if rt({K()}) > {ri(6, 9)}: return")
  of "brk": st(&"if rt({K()}) > {ri(3, 8)}: break")
  of "cont": st(&"if rt({K()}) > {ri(3, 8)}: continue")
  of "mayRaise": setR(&"mayRaise({rn()}, rt({K()}))", 0.6)
  of "early": setR(&"mkEarly(rt({K()}))", 0.5)
  of "vop":
    let vs = live('C')
    let v = touch(vs)
    if v == "": return decl('C')
    if x < 0.3: return ec(&"vval({v})")
    if x < 0.5: return st(&"{v} = V(k: true, r: {rexpr()})")
    if x < 0.65: return st(&"{v} = V(k: false, s: {seqexpr()})")
    if x < 0.8: return st(&"if {v}.k: {v}.r = {rn()}")
    other(vs, v)
  of "wop":
    let ws = live('W')
    let v = touch(ws)
    if v == "": return decl('W')
    if x < 0.3: return ec(&"wval({v})")
    if x < 0.5: return st(&"{v}.x = {rexpr()}")
    if x < 0.65: return st(&"{v}.y.add {rexpr()}")
    if x < 0.8: return st(&"if {v}.y.len > 0: {v}.x = {v}.y[0]")
    other(ws, v)
  of "bop":
    let bs = live('B')
    let v = touch(bs)
    if v == "": return decl('B')
    if x < 0.4: return ec(&"bval({v})")
    if x < 0.6: return st(&"{v}.r = {rexpr()}")
    if x < 0.8: return st(&"{v} = Der(r: {rexpr()}, r2: {v}.r)")
    other(bs, v)
  of "swap":
    var vs = live('R')
    if vs.len < 2: return decl('R')
    r.shuffle(vs)
    st((if x < 0.5: "swap(" else: "swapIt(") & vs[0].name & ", " & vs[1].name & ")")
  of "selfAssign":
    let v = pk('R')
    if v == "": return decl('R')
    if x < 0.5: return st(&"{v} = {v}")
    let p = pk('P')
    if p != "": st(&"{p}.a = {p}.a") else: st(&"{v} = comb({v}, {v})")
  of "identR":
    if x < 0.5: return ec(&"get(ident({rexpr()}))")
    let s = pk('S')
    if s != "": ec(&"sumSeq(ident({s}))") else: ec(&"get(ident({mkK()}))")
  of "if":
    let c = cond()
    if x < 0.6:
      let b = branchy(d, 2)
      st(&"if {c}:", b[0], @[("else:", b[1])])
    else: st(&"if {c}:", branchy(d, 1)[0])
  of "case":
    let b = branchy(d, 3)
    st(&"case rt({K()}) mod 3", @[], @[("of 0:", b[0]), ("of 1:", b[1]), ("else:", b[2])])
  of "while":
    let i = fresh("w")
    st("block:", @[st(&"var {i} = 0"), loop(d, &"while {i} < rt({K()}) mod 4:", @[st(&"inc {i}")])])
  of "for":
    let j = fresh("j")
    loop(d, &"for {j} in 0..<{ri(1, 3)}:")
  of "try":
    let before = moved
    let b = body(d)
    moved = before + moved
    var alts = @[("except:", @[ec("\"caught\"")] & body(d, ri(0, 2)))]
    if rf() < 0.3: alts.add ("finally:", body(d, ri(1, 2)))
    st("try:", b, alts)
  else: st("block:", body(d))

proc generate(seed: int): seq[seq[Node]] =
  r = initRand(seed)
  cnt = 0
  for _ in 0..<ri(4, 7):
    scopes = @[newSeq[Var]()]
    moved.clear; locked.clear
    loopD = 0; closD = 0
    budget = ri(15, 35)
    var b: seq[Node]
    while budget > 0: b.add stmt(0)
    result.add b

# ---- rendering -------------------------------------------------------------------

var prog: seq[seq[Node]]
var only = -1   ## render only proc `t<only>` (reducer)

proc render(n: Node; ind: int; o: var string) =
  let pad = repeat("  ", ind)
  o.add pad & n.line & "\n"
  for k in n.kids: render(k, ind + 1, o)
  if n.line.endsWith(":") and n.kids.len == 0: o.add pad & "  discard\n"
  for (h, ks) in n.alts:
    o.add pad & h & "\n"
    for k in ks: render(k, ind + 1, o)
    if ks.len == 0 and h.endsWith(":"): o.add pad & "  discard\n"

proc render(): string =
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
const Vg = "valgrind -q --leak-check=full --errors-for-leak-kinds=definite --show-leak-kinds=definite --error-exitcode=99 "
const VgKinds = {"Invalid read": "invalid-read", "Invalid write": "invalid-write", "Invalid free": "invalid-free",
  "definitely lost": "def-lost", "uninitialised": "uninit", "Mismatched free": "mismatched-free"}

proc normErr(s: string): string =
  ## the identifying line of an error, numbers replaced by N
  var l = ""
  for x in s.splitLines:
    if x.strip.len > 0: l = x
  for x in s.splitLines:
    if "Error:" in x or "BUG" in x or "Assertion" in x or "SIGSEGV" in x or "Defect" in x:
      l = x.split("Error:")[^1]
      break
  for c in l.strip:
    if c notin Digits: result.add c
    elif not result.endsWith('N'): result.add 'N'
  result.setLen min(result.len, 120)

proc noCounts(o: string): string =
  ## created/destroyed/copies/dups legitimately differ when `when defined(gcOrc)` code runs
  for l in o.splitLines:
    if l.startsWith("SUMMARY"):
      result.add l.split.filterIt(it.startsWith("leaks=") or it.startsWith("errs=")).join(" ")
    else: result.add l
    result.add '\n'

proc check(src: string; cs: seq[string]; vg = true): (seq[string], string) =
  ## build + run `src` under each config: (signatures, details)
  var sig: seq[string]
  var det = ""
  var outs: Table[string, string]
  template hit(x: string) =
    let y = x
    if y notin sig: sig.add y
  writeFile(work / "fz.nim", src)
  for c in cs:
    let dir = work / c
    let exe = dir / "fz"
    let cmd = nimony & " c " & (if c.startsWith("arc"): "--mm:arc" else: "--mm:orc") &
              (if c.endsWith("opt"): " --opt:speed" else: "") & " -d:useLibc --nimcache:" & dir &
              " -o:" & exe & " " & work / "fz.nim"
    removeDir dir
    var (o, rc) = execCmdEx(cmd)
    if rc != 0 and "deps.nif" in o:   # known flake, re-run once
      removeDir dir
      (o, rc) = execCmdEx(cmd)
    if rc != 0 or not fileExists(exe):
      hit &"cfail:{c}:{normErr(o)}"
      det.add &"===== {c}\n{o[max(0, o.len - 3000) .. ^1]}\n"
      continue
    let (p, prc) = execCmdEx("timeout 120 " & (if vg: Vg else: "") & exe & " 2>" & dir / "stderr.txt")
    let e = readFile(dir / "stderr.txt")
    outs[c] = p
    det.add &"===== {c} rc={prc}\n--- stdout tail\n{p[max(0, p.len - 1500) .. ^1]}\n--- stderr tail\n{e[max(0, e.len - 3000) .. ^1]}\n"
    for l in p.splitLines:
      if l.startsWith("ERR ") and " id=" in l: hit "err:" & l[4 ..< l.find(" id=")] & ":" & c
      if l.startsWith("LEAK"): hit &"leak:{c}"
    if "SUMMARY" notin p: hit &"crash:{c}:rc={prc}:{normErr(e)}"
    for (pat, k) in VgKinds:
      if pat in e: hit &"vg:{k}:{c}"
  if "arc" in outs and "orc" in outs and noCounts(outs["arc"]) != noCounts(outs["orc"]): hit "diff:arc-vs-orc"
  for b in ["arc", "orc"]:
    if b in outs and b & "opt" in outs and outs[b] != outs[b & "opt"]: hit &"diff:{b}-vs-{b}opt"
  (sig.sorted, det)

# ---- reducer ---------------------------------------------------------------------

var target = ""
var tests = 0
var maxTests = 150

proc cfgsOf(s: string): seq[string] =
  let p = s.split(':')
  case p[0]
  of "diff": p[1].split("-vs-")
  of "err": @[p[^1]]
  of "vg": @[p[2]]
  else: @[p[1]]

proc still(): bool =
  inc tests
  if tests > maxTests: return false
  result = target in check(render(), cfgsOf(target), target.startsWith("vg:") or target.startsWith("crash:"))[0]
  if result: echo &"  test {tests}: hit, {render().countLines} lines"

proc shrink(l: var seq[Node]): bool =
  ## delete chunks (halves .. single), then hoist or recurse into compound statements
  var c = max(1, l.len div 2)
  while true:
    var i = 0
    while i < l.len:
      let j = min(i + c, l.len)
      let saved = l[i ..< j]
      l.delete(i ..< j)
      if still(): result = true
      else:
        l.insert(saved, i)
        i = j
    if c == 1: break
    c = c div 2
  var i = 0
  while i < l.len:
    let n = l[i]
    var hoisted = false
    if n.kids.len + n.alts.len > 0:
      var bs = @[n.kids]
      for (_, ks) in n.alts:
        if ks.len > 0: bs.add ks
      for b in bs:
        l.delete(i); l.insert(b, i)
        if still():
          hoisted = true
          break
        if b.len > 0: l.delete(i ..< i + b.len)
        l.insert(n, i)
    if hoisted: result = true
    else:
      if shrink(n.kids): result = true
      for a in n.alts.mitems:
        if shrink(a[1]): result = true
      inc i

proc reduce(): string =
  tests = 0
  for i in 0..<prog.len:
    only = i
    if still(): break
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
  var want = ""
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": work = val
    of "budget": maxTests = parseInt(val)
    of "sig": want = val
    of "noreduce": doReduce = false
    else: quit "unknown option: " & key
  if work == "": work = getAppDir() / "work" / ("s" & $seed)  # one per process
  nimony = absolutePath(nimony)
  work = absolutePath(work)
  outDir = absolutePath(outDir)
  createDir work
  createDir outDir
  let t0 = epochTime()
  var found = 0
  for k in 0..<count:
    let s = seed + k
    prog = generate(s)
    only = -1
    let t1 = epochTime()
    let (sig, det) = check(render(), @["arc", "orc", (if s mod 2 == 0: "arcopt" else: "orcopt")])
    let el = int(epochTime() - t0)
    if sig.len == 0:
      echo &"[{el}s] seed {s}: ok ({int(epochTime() - t1)}s)"
      continue
    inc found
    echo &"[{el}s] seed {s}: " & sig.join(" ")
    let d = outDir / &"s{s}"
    createDir d
    writeFile(d / "prog.nim", render())
    writeFile(d / "details.txt", sig.join("\n") & "\n\n" & det)
    let f = open(outDir / "log.csv", fmAppend)
    f.writeLine(&"{el},{k + 1},{s},\"" & sig.join("+") & "\"")
    f.close
    if not doReduce: continue
    target = want
    if target notin sig:
      target = ""
      for p in ["err:", "vg:", "crash:", "cfail:", "leak:", "diff:"]:
        for x in sig:
          if target == "" and x.startsWith(p): target = x
    echo &"  reducing {target}"
    let red = reduce()
    writeFile(d / "reduced.nim", red)
    echo &"  reduced to {red.countLines} lines in {tests} tests: {d}/reduced.nim"
  echo &"{count} programs, {found} with findings, {int(epochTime() - t0)}s -> {outDir}"
  if found > 0: quit 1

main()
