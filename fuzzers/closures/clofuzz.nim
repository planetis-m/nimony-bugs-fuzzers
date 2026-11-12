## Closure/iterator fuzzer for Nimony, with a reference interpreter.
##
## Generates random programs over closures (literals, factories returning a
## closure, closures in seqs and in objects), inline, `.closure` and local
## iterators, `defer`, `try/except/finally` and `raise`. A program is a
## statement tree: every node both EMITS Nimony source and RUNS in a small
## interpreter (`model`), so the expected output of every program -- and of
## every variant the reducer tries -- is known without trusting a compiler.
## Each program is compiled with `nimony c` and `nimony n`, run, and its
## output compared with the model.
##
## What a program may contain is chosen so the expected output is unambiguous:
##
## * ints only, every value in [0, 997): arithmetic is `mod 997`;
## * closures capture by reference; a closure that escapes a loop body only
##   captures variables declared outside that loop, so "env per iteration"
##   vs. "env per proc" cannot change the result;
## * a `for` over an iterator behaves as if the iterator were inlined: the
##   loop body runs at each `yield` (a callback), and leaving the loop (break,
##   return, raise) unwinds through the iterator as an `Escape`, which runs its
##   pending finally/defer but is never caught by its `except`; a loop over an
##   inline iterator that yields inside `try/except` never raises;
## * closure iterators never yield inside a defer/finally scope; `echo` args
##   never contain calls.
##
## A finding is a signature: backend + normalized first error line, exit
## code, or `mismatch`. The first program of each new signature is saved
## under `--out` and reduced: chunks of definitions and statements are
## deleted while the model still accepts the program and the signature
## persists. `--avoid:citer-in-citer,unused-local-iter` steers around two
## known crashes (findings/01.md, 02.md).
##
##   nim c -d:release -o:closures/clofuzz closures/clofuzz.nim
##   closures/clofuzz --seed:1 --count:20
##   closures/clofuzz --seed:17 --count:1           # reproduce one
##
## Parallelism: start several processes with disjoint seed ranges.

import std / [os, osproc, strutils, random, times, strformat, parseopt, sequtils, tables]
from std/posix import getrusage, Rusage, RUSAGE_CHILDREN

type
  K = enum
    eLit, eVar, eAdd, eMul, eSub, eLt, eEq, eEven,
    sEcho, sEchoErr, sDecl, sAsgn, sCall, sIf, sCase, sWhile, sFor, sForIt,
    sBreak, sCont, sRet, sRaise, sReraise, sYield, sDefer, sTry,
    sClo, sCloSet, sSeq, sSeqAdd, sBox, sBoxSet, sIter, sFacRes,
    cLit, cVar, cFac,        ## closure sources: literal, variable, factory call
    dFac, dUnit              ## top level: factory proc, test proc `u<i>`

  N = ref object
    k: K
    s, t: string             ## names: variable, tag, callee, iterator, ...
    n, m: int                ## literal, loop bound, callee kind + seq index, unit args
    a: seq[N]                ## expressions
    b: seq[seq[N]]           ## statement lists: what the reducer shrinks
    src: N                   ## closure source; a factory's literal
    ps: seq[string]          ## iterator params
    clo, guarded, cleanup, mayRaise: bool  ## iterator facts

const Codes = ["SyntaxError", "IOError", "RangeError", "ValueError"]

# ---- emitting ----------------------------------------------------------------

proc es(e: N): string =
  template x(i): string = es(e.a[i])
  case e.k
  of eLit: $e.n
  of eVar: e.s
  of eAdd: "((" & x(0) & " + " & x(1) & ") mod 997)"
  of eMul: "((" & x(0) & " * " & x(1) & ") mod 997)"
  of eSub: "((" & x(0) & " + 997 - " & x(1) & ") mod 997)"
  of eLt: x(0) & " < " & x(1)
  of eEq: x(0) & " == " & x(1)
  of eEven: x(0) & " mod 2 == 0"
  else: "?"

proc emit(s: N; ind: int; o: var seq[string])

proc emit(l: seq[N]; ind: int; o: var seq[string]) =
  if l.len == 0: o.add repeat("  ", ind) & "discard"
  for s in l: emit(s, ind, o)

const cloHead = "proc (Y: int): int {.closure, raises.} ="

proc emitSrc(pre: string; c: N; ind: int; o: var seq[string]) =
  let p = repeat("  ", ind)
  case c.k
  of cLit:
    o.add p & pre & cloHead.replace("Y", c.s)
    o.add p & "  result = 0"
    emit(c.b[0], ind + 1, o)
  of cVar: o.add p & pre & c.s
  else: o.add p & pre & c.s & "(" & es(c.a[0]) & ")"

proc emit(s: N; ind: int; o: var seq[string]) =
  let p = repeat("  ", ind)
  template ln(x: string) = o.add p & x
  template sub(i: int) = emit(s.b[i], ind + 1, o)
  case s.k
  of sEcho: ln "echo \"" & s.s & " \", " & es(s.a[0])
  of sEchoErr: ln "echo \"" & s.s & " \", " & s.t
  of sDecl: ln "var " & s.s & " = " & es(s.a[0])
  of sAsgn: ln s.s & " = " & es(s.a[0])
  of sCall:
    let callee = [s.t, s.t & "[" & $s.m & "]", s.t & ".f"][s.n]
    ln (if s.n == 1: "if " & s.t & ".len > " & $s.m & ": " else: "") &
       (if s.s != "": s.s & " = " else: "discard ") & callee & "(" & es(s.a[0]) & ")"
  of sIf:
    ln "if " & es(s.a[0]) & ":"; sub 0
    if s.b[1].len > 0: ln "else:"; sub 1
  of sCase:
    ln "case (" & es(s.a[0]) & ") mod 3"
    ln "of 0:"; sub 0
    ln "of 1:"; sub 1
    ln "else:"; sub 2
  of sWhile:
    ln "var " & s.s & " = 0"
    ln "while " & s.s & " < " & $s.n & ":"
    ln "  inc " & s.s
    sub 0
  of sFor: ln "for " & s.s & " in 0 ..< " & $s.n & ":"; sub 0
  of sForIt: ln "for " & s.s & " in " & s.t & "(" & s.a.mapIt(es(it)).join(", ") & "):"; sub 0
  of sBreak: ln "break"
  of sCont: ln "continue"
  of sRet: ln "return"
  of sRaise: ln "raise " & s.s
  of sReraise: ln "raise"
  of sYield: ln "yield " & es(s.a[0])
  of sDefer: ln "defer:"; sub 0
  of sTry:
    ln "try:"; sub 0
    if s.s != "": ln "except ErrorCode as " & s.s & ":"; sub 1
    if s.n == 1: ln "finally:"; sub 2
  of sClo: emitSrc("var " & s.s & ": CT = ", s.src, ind, o)
  of sCloSet: emitSrc(s.s & " = ", s.src, ind, o)
  of sSeq: ln "var " & s.s & ": seq[CT] = @[]"
  of sSeqAdd: emitSrc(s.s & ".add ", s.src, ind, o)
  of sBox: emitSrc("var " & s.s & " = Box(f: ", s.src, ind, o); o[^1].add ")"
  of sBoxSet: emitSrc(s.s & ".f = ", s.src, ind, o)
  of sIter:
    ln "iterator " & s.s & "(" & s.ps.mapIt(it & ": int").join(", ") & "): int {." &
       (if s.clo: "closure, " else: "") & "raises, sideEffect.} ="
    sub 0
  of dFac:
    ln "proc " & s.s & "(" & s.t & ": int): CT {.raises.} ="
    sub 0
    ln "  result = " & cloHead.replace("Y", s.src.s)
    ln "    result = 0"
    emit(s.src.b[0], ind + 2, o)
    for x in s.b[1]: emit(x, ind + 1, o)
  of dUnit: ln "proc " & s.s & "(p0, p1: int) {.raises.} ="; sub 0
  else: discard

proc render(p: seq[N]): string =
  var o = @["import std/syncio", "", "type", "  CT = " & cloHead.replace("Y", "y")[0 .. ^3],
            "  Box = object", "    f: CT", ""]
  for d in p: emit(d, 0, o); o.add ""
  for d in p:
    if d.k == dUnit:
      o.add ["try:", &"  {d.s}({d.n}, {d.m})", "except ErrorCode as e:", &"  echo \"{d.s} exc \", e"]
  o.join("\n") & "\n"

# ---- the model ---------------------------------------------------------------

type
  VK = enum vNil, vInt, vClo, vSeq, vBox, vErr, vIter
  V = object
    k: VK
    i: int
    e: string                ## error code
    f: N                     ## closure literal or iterator definition
    env: Sc
    sq: seq[V]               ## seq elements; a box is a one-element seq
  Cell = ref object
    v: V
  Sc = ref object
    vars: seq[(string, Cell)]
    up: Sc
  Yf = proc (v: int)         ## the loop body a `yield` runs
  Fuel = object of CatchableError
  Invalid = object of CatchableError
  BreakX = object of CatchableError
  ContX = object of CatchableError
  RetX = object of CatchableError
  NimErr = object of CatchableError
  Escape = object of CatchableError  ## leaves loop `id` through its iterator
    id: int
    inner: ref CatchableError

var mout: seq[string]
var fuel, depth, escIds: int
var iters, facs: Table[string, N]

proc inv(m: string) {.noreturn.} = raise newException(Invalid, m)
proc tick() =
  dec fuel
  if fuel < 0 or mout.len > 4000: raise newException(Fuel, "")

proc look(sc: Sc; n: string): Cell =
  var s = sc
  while s != nil:
    for i in countdown(s.vars.high, 0):
      if s.vars[i][0] == n: return s.vars[i][1]
    s = s.up
  inv "undeclared " & n

proc decl(sc: Sc; n: string; v: V) = sc.vars.add (n, Cell(v: v))
proc vi(x: int): V = V(k: vInt, i: x)
proc ival(c: Cell): int =
  if c.v.k != vInt: inv "not an int"
  c.v.i
proc setInt(sc: Sc; n: string; x: int) =
  let c = look(sc, n)
  discard ival(c)
  c.v = vi(x)

proc ev(e: N; sc: Sc): int =
  template x(i): int = ev(e.a[i], sc)
  case e.k
  of eLit: e.n
  of eVar: ival(look(sc, e.s))
  of eAdd: (x(0) + x(1)) mod 997
  of eMul: (x(0) * x(1)) mod 997
  of eSub: (x(0) + 997 - x(1)) mod 997
  of eLt: ord(x(0) < x(1))
  of eEq: ord(x(0) == x(1))
  of eEven: ord(x(0) mod 2 == 0)
  else: inv "not an expression"

proc runList(l: seq[N]; sc: Sc; y: Yf)

proc callClo(c: V; arg: int): int =
  tick()
  inc depth
  if depth > 60: raise newException(Fuel, "")
  try:
    let s = Sc(up: c.env)
    s.decl(c.f.s, vi(arg))
    s.decl("result", vi(0))
    try: runList(c.f.b[0], s, nil)
    except RetX: discard
    result = ival(look(s, "result"))
  finally: dec depth

proc srcVal(c: N; sc: Sc): V =
  case c.k
  of cLit: V(k: vClo, f: c, env: sc)
  of cVar:
    let v = look(sc, c.s).v
    if v.k != vClo: inv "not a closure"
    v
  else:
    if c.s notin facs: inv "no factory"
    let f = facs[c.s]
    let a = ev(c.a[0], sc)
    tick()
    let s = Sc()
    s.decl(f.t, vi(a))
    s.decl("result", V())
    # one list: a `defer` in the prologue covers the rest of the proc
    runList(f.b[0] & @[N(k: sFacRes, src: f.src)] & f.b[1], s, nil)
    look(s, "result").v

proc setVal(sc: Sc; n: string; k: VK; v: V) =
  let c = look(sc, n)
  if c.v.k != k: inv "wrong kind: " & n
  case k
  of vSeq: c.v.sq.add v
  of vBox: c.v.sq[0] = v
  else: c.v = v

proc loopBody(l: seq[N]; sc: Sc; y: Yf): bool =
  try: runList(l, sc, y)
  except ContX: discard
  except BreakX: result = true

proc run(s: N; sc: Sc; y: Yf) =
  case s.k
  of sEcho: mout.add s.s & " " & $ev(s.a[0], sc)
  of sEchoErr:
    let v = look(sc, s.t).v
    if v.k != vErr: inv "not an error"
    mout.add s.s & " " & v.e
  of sDecl: sc.decl(s.s, vi(ev(s.a[0], sc)))
  of sAsgn: sc.setInt(s.s, ev(s.a[0], sc))
  of sCall:
    let c = look(sc, s.t).v
    var f = c
    if s.n > 0:
      if c.k != [vNil, vSeq, vBox][s.n]: inv "not a seq/box"
      if s.n == 1 and s.m >= c.sq.len: return
      f = c.sq[if s.n == 1: s.m else: 0]
    if f.k != vClo: inv "not a closure"
    let r = callClo(f, ev(s.a[0], sc))
    if s.s != "": sc.setInt(s.s, r)
  of sIf: runList(s.b[if ev(s.a[0], sc) != 0: 0 else: 1], Sc(up: sc), y)
  of sCase: runList(s.b[ev(s.a[0], sc) mod 3], Sc(up: sc), y)
  of sWhile:
    sc.decl(s.s, vi(0))
    let c = look(sc, s.s)
    while c.v.i < s.n:
      tick()
      inc c.v.i
      if loopBody(s.b[0], Sc(up: sc), y): break
  of sFor:
    for i in 0 ..< s.n:
      tick()
      let s2 = Sc(up: sc)
      s2.decl(s.s, vi(i))
      if loopBody(s.b[0], s2, y): break
  of sForIt:
    var d = iters.getOrDefault(s.t)
    var env: Sc = nil
    if d == nil:
      let v = look(sc, s.t).v
      if v.k != vIter: inv "no iterator " & s.t
      d = v.f
      env = v.env
    if d.ps.len != s.a.len: inv "arity"
    let isc = Sc(up: env)
    for j, p in d.ps: isc.decl(p, vi(ev(s.a[j], sc)))
    inc escIds
    let id = escIds
    let cb = proc (v: int) =
      tick()
      let s2 = Sc(up: sc)
      s2.decl(s.s, v.vi)
      try: runList(s.b[0], s2, y)
      except ContX: discard
      except CatchableError as e: raise (ref Escape)(id: id, inner: e)
    try:
      try: runList(d.b[0], isc, cb)
      except RetX: discard
    except Escape as e:
      if e.id != id: raise
      if not (e.inner of BreakX): raise e.inner
  of sBreak: raise newException(BreakX, "")
  of sCont: raise newException(ContX, "")
  of sRet: raise newException(RetX, "")
  of sRaise: raise newException(NimErr, s.s)
  of sReraise:
    let v = look(sc, s.s).v
    if v.k != vErr: inv "reraise"
    raise newException(NimErr, v.e)
  of sYield:
    if y == nil: inv "yield outside of an iterator"
    y(ev(s.a[0], sc))
  of sTry:
    try:
      try: runList(s.b[0], Sc(up: sc), y)
      except NimErr as e:
        if s.s == "": raise
        let s2 = Sc(up: sc)
        s2.decl(s.s, V(k: vErr, e: e.msg))
        runList(s.b[1], s2, y)
    finally:
      if s.n == 1: runList(s.b[2], Sc(up: sc), nil)
  of sClo: sc.decl(s.s, srcVal(s.src, sc))
  of sCloSet: sc.setVal(s.s, vClo, srcVal(s.src, sc))
  of sSeq: sc.decl(s.s, V(k: vSeq))
  of sSeqAdd: sc.setVal(s.s, vSeq, srcVal(s.src, sc))
  of sBox: sc.decl(s.s, V(k: vBox, sq: @[srcVal(s.src, sc)]))
  of sBoxSet: sc.setVal(s.s, vBox, srcVal(s.src, sc))
  of sIter: sc.decl(s.s, V(k: vIter, f: s, env: sc))
  of sFacRes: look(sc, "result").v = V(k: vClo, f: s.src, env: sc)
  else: inv "not a statement"

proc runList(l: seq[N]; sc: Sc; y: Yf) =
  for i, s in l:
    if s.k == sDefer:
      try: runList(l[i+1 .. ^1], sc, y)
      finally: runList(s.b[0], Sc(up: sc), nil)
      return
    tick()
    run(s, sc, y)

proc model(p: seq[N]): seq[string] =
  ## Expected output; raises Invalid or Fuel.
  mout = @[]
  fuel = 30000
  depth = 0
  iters.clear
  facs.clear
  for d in p:
    if d.k == sIter: iters[d.s] = d
    if d.k == dFac: facs[d.s] = d
  for d in p:
    if d.k != dUnit: continue
    let sc = Sc()
    sc.decl("p0", vi(d.n))
    sc.decl("p1", vi(d.m))
    try: runList(d.b[0], sc, nil)
    except RetX: discard
    except NimErr as e: mout.add d.s & " exc " & e.msg
    except BreakX, ContX: inv "stray break"
  mout

# ---- the generator -----------------------------------------------------------

type
  GK = enum gInt, gClo, gSeq, gBox, gErr
  GV = object
    name: string
    k: GK
    depth, maxcap: int       ## loop depth of the declaration; a closure's capture limit
    ro: bool
  Ctx = object
    routine: string          ## unit clo iter citer fac
    vars: seq[GV]
    iters, facs: seq[N]
    depth, nest: int
    inLoop, noRaise, canYield, exceptGuard, pure: bool
    idef: N                  ## the iterator being generated

var r: Rand
var fresh: int
var small: bool
var avoid = ""

proc nm(p: string): string = inc fresh; p & $fresh
proc ch(p: float): bool = r.rand(1.0) < p
proc ri(a, b: int): int = r.rand(a..b)
proc ctx(routine: string; vars: seq[GV]; its, fs: seq[N]): Ctx =
  Ctx(routine: routine, vars: vars, iters: its, facs: fs, canYield: routine in ["iter", "citer"])
proc child(c: Ctx): Ctx = (result = c; inc result.nest)
proc loopc(c: Ctx): Ctx = (result = child(c); inc result.depth; result.inLoop = true)
proc purec(c: Ctx): Ctx = (result = child(c); result.pure = true; result.canYield = false)
proc E(k: K; a: varargs[N]): N = N(k: k, a: @a)
proc L(x: int): N = N(k: eLit, n: x)
proc gv(n: string; k = gInt; depth = 0; ro = false; maxcap = -1): GV =
  GV(name: n, k: k, depth: depth, ro: ro, maxcap: maxcap)

proc expr(c: Ctx; d = 2): N =
  let vs = c.vars.filterIt(it.k == gInt)
  if d <= 0 or ch(0.35):
    if vs.len > 0 and ch(0.7): return N(k: eVar, s: r.sample(vs).name)
    return L(ri(0, 12))
  E(r.sample([eAdd, eAdd, eMul, eSub]), expr(c, d - 1), expr(c, d - 1))

proc cond(c: Ctx): N =
  case r.sample([eLt, eEq, eEven, eLt])
  of eEven: E(eEven, expr(c, 1))
  of eEq: E(eEq, expr(c, 1), L(ri(0, 6)))
  else: E(eLt, expr(c, 1), expr(c, 1))

proc echoS(c: Ctx): N =
  let errs = c.vars.filterIt(it.k == gErr)
  if errs.len > 0 and ch(0.3): N(k: sEchoErr, s: nm("t"), t: r.sample(errs).name)
  else: N(k: sEcho, s: nm("t"), a: @[expr(c)])

proc capt(c: Ctx; limit: int): seq[GV] =
  ## What a closure created in `c` may see: captured values are read-only.
  for v in c.vars:
    if v.k != gErr and v.name != "result" and v.depth <= limit:
      result.add gv(v.name, v.k, -1, v.ro or v.k != gInt)

proc stmts(c: var Ctx; n: int): seq[N]
proc body(c: Ctx): seq[N] =
  var c = c
  stmts(c, ri(1, if c.nest > 1: 2 else: 3))

proc cloLit(c: Ctx; limit: int): N =
  ## A closure literal capturing only variables of loop depth <= limit.
  var vis = capt(c, limit)
  let p = nm("y")
  vis.add [gv(p, ro = true), gv("result")]
  var cc = ctx("clo", vis, c.iters, c.facs)
  cc.nest = c.nest + 1
  var b = stmts(cc, ri(1, 3))
  b.add N(k: sAsgn, s: "result", a: @[E(eAdd, N(k: eVar, s: "result"), expr(cc, 1))])
  N(k: cLit, s: p, b: @[b])

proc cloSrc(c: Ctx; limit: int; allowLit = true): N =
  var opts: seq[K]
  if allowLit and c.nest < 5: opts.add [cLit, cLit]
  let cvs = c.vars.filterIt(it.k == gClo and it.maxcap <= limit)
  if cvs.len > 0: opts.add cVar
  if c.facs.len > 0 and not c.noRaise: opts.add cFac
  if opts.len == 0: return nil
  case r.sample(opts)
  of cLit: cloLit(c, limit)
  of cVar: N(k: cVar, s: r.sample(cvs).name)
  else: N(k: cFac, s: r.sample(c.facs).s, a: @[expr(c, 1)])

proc cloDecl(c: var Ctx): N =
  let n = nm("c")
  let own = c.vars.filterIt(it.k == gClo and not it.ro)
  if own.len > 0 and ch(0.3):
    let v = r.sample(own)
    let src = cloSrc(c, min(v.maxcap, c.depth))
    if src != nil: return N(k: sCloSet, s: v.name, src: src)
  let mc = ri(-1, c.depth)
  let src = cloSrc(c, mc)
  if src == nil: return echoS(c)
  c.vars.add gv(n, gClo, c.depth, maxcap = mc)
  N(k: sClo, s: n, src: src)

proc walk(l: seq[N]; res: var seq[N]) =
  for s in l:
    res.add s
    for k in s.b: walk(k, res)
    if s.src != nil and s.src.k == cLit: walk(s.src.b[0], res)

proc find(its: seq[N]; n: string): N =
  for d in its:
    if d.s == n: return d

proc hasCleanup(l, its: seq[N]): bool =
  var all: seq[N]
  walk(l, all)
  for s in all:
    if s.k == sDefer or (s.k == sTry and s.n == 1): return true
    if s.k == sForIt and its.find(s.t) != nil and its.find(s.t).cleanup: return true

proc mayRaise(l, its: seq[N]): bool =
  var all: seq[N]
  walk(l, all)
  for s in all:
    if s.k in {sRaise, sReraise, sCall}: return true
    if s.k in {sClo, sCloSet, sBox, sSeqAdd, sBoxSet} and s.src.k == cFac: return true
    if s.k == sForIt and (its.find(s.t) == nil or its.find(s.t).mayRaise): return true

proc iterdef(name: string; cl: bool; outer: seq[GV]; its, fs: seq[N]; nest = 0): N =
  result = N(k: sIter, s: name, clo: cl)
  var vs = outer
  for i in 0 ..< ri(0, 2):
    result.ps.add nm("a")
    vs.add gv(result.ps[^1], ro = true)
  var c = ctx(if cl: "citer" else: "iter", vs, its, fs)
  c.idef = result
  c.nest = nest
  var b = stmts(c, ri(2, 5))
  if not b.anyIt(it.k == sYield): b.add N(k: sYield, a: @[expr(c)])
  result.b = @[b]
  result.cleanup = hasCleanup(b, its)
  result.mayRaise = mayRaise(b, its)

proc forIt(c: Ctx; d: N): N =
  var d = d
  if d == nil:
    let its = c.iters.filterIt(not (c.noRaise and it.mayRaise))
    if its.len == 0: return echoS(c)
    d = r.sample(its)
  elif c.noRaise and d.mayRaise: return echoS(c)
  let v = nm("x")
  var lc = loopc(c)
  lc.vars.add gv(v, depth = lc.depth, ro = true)
  if d.guarded: (lc.noRaise = true; lc.exceptGuard = true)
  if c.routine == "citer" and d.cleanup: lc.canYield = false
  var args: seq[N]
  for p in d.ps: args.add expr(c, 1)
  N(k: sForIt, s: v, t: d.s, a: args, b: @[body(lc)])

proc callees(c: Ctx): seq[(int, string)] =
  for v in c.vars:
    case v.k
    of gClo: result.add (0, v.name)
    of gSeq: result.add (1, v.name)
    of gBox: result.add (2, v.name)
    else: discard

proc stmt(c: var Ctx): seq[N] =
  template one(x: N) = return @[x]
  template maybeIf(x: N; p = 0.7) = one(if ch(p): N(k: sIf, a: @[cond(c)], b: @[@[x], @[]]) else: x)
  let ints = c.vars.filterIt(it.k == gInt and not it.ro)
  if c.pure:
    if ints.len > 0 and ch(0.3): one N(k: sAsgn, s: r.sample(ints).name, a: @[expr(c)])
    one N(k: sEcho, s: nm("t"), a: @[expr(c)])
  var w = @[("echo", 5), ("decl", 3), ("assign", if ints.len > 0: 3 else: 0)]
  if c.nest < (if small: 2 else: 3):
    w.add [("if", 3), ("case", 1), ("while", 1), ("for", 1), ("foriter", if c.iters.len > 0: 5 else: 0),
           ("try", 2), ("defer", if c.routine == "citer": 0 else: 2), ("clodecl", 3), ("seq", 1),
           ("box", 1), ("localiter", 1)]
  if not c.noRaise: w.add [("call", if callees(c).len > 0: 4 else: 0), ("raise", 1)]
  if c.inLoop: w.add [("break", 1), ("continue", 1)]
  if c.routine != "fac": w.add ("return", 1)
  if c.canYield: w.add ("yield", 6)
  var p = r.rand(w.mapIt(it[1]).foldl(a + b) - 1)
  var key = ""
  for (k, x) in w:
    if p < x: (key = k; break)
    p -= x
  case key
  of "echo": one echoS(c)
  of "decl":
    let n = nm("v")
    let e = expr(c)
    c.vars.add gv(n, depth = c.depth)
    one N(k: sDecl, s: n, a: @[e])
  of "assign": one N(k: sAsgn, s: r.sample(ints).name, a: @[expr(c)])
  of "if":
    let e = cond(c)
    let a = body(child(c))
    one N(k: sIf, a: @[e], b: @[a, if ch(0.5): body(child(c)) else: newSeq[N]()])
  of "case":
    let e = expr(c, 1)
    one N(k: sCase, a: @[e], b: @[body(child(c)), body(child(c)), body(child(c))])
  of "while":
    let n = nm("w")
    c.vars.add gv(n, depth = c.depth, ro = true)
    one N(k: sWhile, s: n, n: ri(1, 4), b: @[body(loopc(c))])
  of "for":
    let v = nm("i")
    var lc = loopc(c)
    lc.vars.add gv(v, depth = lc.depth, ro = true)
    one N(k: sFor, s: v, n: ri(0, 4), b: @[body(lc)])
  of "foriter": one forIt(c, nil)
  of "try":
    let hasExc = ch(0.75)
    let hasFin = not hasExc or ch(0.5)
    var bc = child(c)
    bc.exceptGuard = bc.exceptGuard or hasExc
    if hasFin and c.routine == "citer": bc.canYield = false
    let bd = body(bc)
    var en = ""
    var h, f: seq[N]
    if hasExc:
      en = nm("e")
      var hc = child(c)
      if hasFin and c.routine == "citer": hc.canYield = false
      hc.vars.add gv(en, gErr, c.depth)
      h = body(hc)
      if not c.noRaise and ch(0.2): h.add N(k: sReraise, s: en)
    if hasFin: f = body(purec(c))
    one N(k: sTry, s: en, n: ord(hasFin), b: @[bd, h, f])
  of "defer": one N(k: sDefer, b: @[body(purec(c))])
  of "clodecl": one cloDecl(c)
  of "seq":
    let ss = c.vars.filterIt(it.k == gSeq and not it.ro)
    if ss.len > 0 and ch(0.7):
      let v = r.sample(ss)
      let src = cloSrc(c, v.depth)
      if src != nil: one N(k: sSeqAdd, s: v.name, src: src)
    let n = nm("s")
    c.vars.add gv(n, gSeq, c.depth)
    one N(k: sSeq, s: n)
  of "box":
    let bs = c.vars.filterIt(it.k == gBox and not it.ro)
    if bs.len > 0 and ch(0.5):
      let v = r.sample(bs)
      let src = cloSrc(c, v.depth)
      if src != nil: one N(k: sBoxSet, s: v.name, src: src)
    let src = cloSrc(c, c.depth, allowLit = false)
    if src == nil: one cloDecl(c)
    let n = nm("b")
    c.vars.add gv(n, gBox, c.depth)
    one N(k: sBox, s: n, src: src)
  of "localiter":
    if c.nest > 2: one echoS(c)
    let cl = ch(0.5) and not ("citer-in-citer" in avoid and c.routine == "citer")
    # a local INLINE iterator may not touch the enclosing routine's locals
    let d = iterdef(nm("li"), cl, if cl: capt(c, high(int)) else: newSeq[GV](), c.iters, c.facs, c.nest + 1)
    c.iters.add d
    if "unused-local-iter" in avoid: return @[d, forIt(c, d)]
    one d
  of "call":
    let (ck, cn) = r.sample(callees(c))
    let tgt = if ints.len > 0 and ch(0.75): r.sample(ints).name else: ""
    one N(k: sCall, s: tgt, t: cn, n: ck, m: ri(0, 2), a: @[expr(c, 1)])
  of "raise": maybeIf N(k: sRaise, s: r.sample(Codes))
  of "break": maybeIf N(k: sBreak)
  of "continue": maybeIf N(k: sCont)
  of "return": maybeIf(N(k: sRet), 2.0)
  else:
    if c.exceptGuard and c.idef != nil and not c.idef.clo: c.idef.guarded = true
    one N(k: sYield, a: @[expr(c)])

proc stmts(c: var Ctx; n: int): seq[N] =
  for i in 0 ..< n: result.add stmt(c)

proc factory(name: string; fs: seq[N]): N =
  let p = nm("a")
  var c = ctx("fac", @[gv(p, ro = true)], @[], fs)
  c.noRaise = true           # `result` is not set yet: a raise would leave it unproven
  let pre = stmts(c, ri(1, 3))
  c.noRaise = false
  let lit = cloLit(c, 0)
  N(k: dFac, s: name, t: p, src: lit, b: @[pre, stmts(c, ri(0, 2))])

proc generate(seed: int): (seq[N], seq[string]) =
  ## A program and its expected output; retries sub-seeds until it terminates.
  for sub in 0 ..< 50:
    r = initRand(seed * 1000 + sub + 1)
    fresh = 0
    small = r.rand(1.0) < 0.6  # most programs are small: one crash hides less
    var p: seq[N]
    for u in 0 ..< (if small: 1 else: ri(1, 3)):
      let un = "u" & $u
      var its, fs: seq[N]
      for j in 0 ..< ri(0, if small: 1 else: 3):
        fs.add factory(un & "_mk" & $j, fs)
        p.add fs[^1]
      for j in 0 ..< ri(1, if small: 2 else: 3):
        its.add iterdef(un & "_it" & $j, ch(0.3), @[], its, fs)
        p.add its[^1]
      var c = ctx("unit", @[gv("p0", ro = true), gv("p1", ro = true)], its, fs)
      let b = stmts(c, if small: ri(3, 5) else: ri(4, 8))
      p.add N(k: dUnit, s: un, b: @[b], n: ri(0, 9), m: ri(0, 9))
    try: return (p, model(p))
    except Fuel: discard
  raise newException(Fuel, "no terminating program for seed " & $seed)

# ---- running -----------------------------------------------------------------

var nimony = "/home/ageralis/Projects/nimony/bin/nimony"
var work = ""

proc norm(s: string): string =
  ## Error line without paths and generated names: `c12.0` -> `ID.N`.
  var words = s.strip.split(' ')
  for w in words.mitems:
    let a = w.find('/')
    let b = w.rfind('/')
    if a < b: w = w[0 ..< a] & w[b+1 .. ^1]
  let t = words.join(" ")
  var i = 0
  while i < t.len and result.len < 160:
    if t[i] in IdentChars:
      var j = i
      while j < t.len and t[j] in IdentChars: inc j
      let tok = t[i ..< j]
      result.add(if tok.allIt(it in Digits): "N" elif tok.anyIt(it in Digits): "ID" else: tok)
      i = j
    else:
      result.add t[i]
      inc i

proc compileSig(o: string): string =
  for pat in ["[Bug]", "Error: unhandled exception: ", "SIGSEGV", "Assertion", "error: ", "Error: "]:
    for l in o.splitLines:
      if pat in l: return norm(l[l.find(pat) .. ^1])
  "failed:" & norm(o.strip.splitLines[^1])

proc build(src, backend: string): (string, string) =
  ## (executable or "", compiler output); the nimcache is kept between programs.
  let nc = work / backend
  for f in walkDirRec(nc):
    if f.extractFilename == "prog": removeFile f
  let (o, rc) = execCmdEx(&"timeout 300 {nimony.quoteShell} {backend} --nimcache:{nc.quoteShell} {src.quoteShell}",
                          workingDir = work)
  if rc == 124: return ("", "compile-timeout")
  if rc == 0:
    for f in walkDirRec(nc):
      if f.extractFilename == "prog" and fpUserExec in getFilePermissions(f): return (f, o)
  ("", o)

proc check(p: seq[N]; exp: seq[string]; want = ""): seq[(string, string)] =
  ## (signature, detail) for every backend that disagrees with the model.
  let src = work / "prog.nim"
  writeFile(src, render(p))
  for b in ["c", "n"]:
    if want != "" and not want.startsWith(b & ":"): continue
    var (exe, o) = build(src, b)
    if exe == "" and "cannot open" in o and "deps.nif" in o: (exe, o) = build(src, b)  # known flake
    if exe == "":
      result.add (b & ":compile:" & (if o == "compile-timeout": o else: compileSig(o)), o)
      if b == "c": break     # broken for the native backend too
      continue
    let (ro, rc) = execCmdEx("timeout 15 " & exe.quoteShell)
    var got = ro.splitLines
    if got.len > 0 and got[^1] == "": got.setLen(got.len - 1)
    if rc == 124: result.add (b & ":run-timeout", ro)
    elif rc != 0: result.add (&"{b}:exit{rc}:" & norm(if got.len > 0: got[^1] else: ""), ro)
    elif got != exp:
      var i = 0
      while i < min(got.len, exp.len) and got[i] == exp[i]: inc i
      let e = if i < exp.len: exp[i] else: "<eof>"
      let g = if i < got.len: got[i] else: "<eof>"
      result.add (b & ":mismatch", &"line {i+1}: expected {e} got {g}\n{ro}")

# ---- reduction ---------------------------------------------------------------

var red: seq[N]              ## the program being reduced
var redSig: string
var tests, budget = 0

proc still(): bool =
  if tests >= budget: return false
  var exp: seq[string]
  try: exp = model(red)
  except CatchableError: return false
  inc tests
  check(red, exp, redSig).anyIt(it[0] == redSig)

proc shrink(l: var seq[N]): bool =
  ## Delete halves, quarters, ... single statements while the failure persists;
  ## then recurse into the remaining statements' bodies.
  var chunk = max(1, l.len div 2)
  while chunk >= 1 and l.len > 0:
    var i = 0
    while i < l.len:
      let saved = l[i ..< min(i + chunk, l.len)]
      l.delete(i ..< min(i + chunk, l.len))
      if still(): result = true
      else:
        l.insert(saved, i)
        i += chunk
    chunk = chunk div 2
  for s in l:
    for j in 0 ..< s.b.len:
      if shrink(s.b[j]): result = true
    if s.src != nil and s.src.k == cLit and shrink(s.src.b[0]): result = true

proc reduce(p: seq[N]; sig: string): seq[N] =
  red = p
  redSig = sig
  tests = 0
  for round in 0 ..< 5:
    if not shrink(red): break
  red

# ---- driver ------------------------------------------------------------------

proc main() =
  var seed = 1
  var count = 10
  var outDir = getAppDir() / "out"
  var doReduce = true
  budget = 100
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": work = val
    of "avoid": avoid = val
    of "budget": budget = parseInt(val)
    of "noreduce": doReduce = false
    else: quit "unknown option: " & key
  if work == "": work = getAppDir() / "work" / ("s" & $seed)
  work = absolutePath(work)
  nimony = absolutePath(nimony)
  createDir(work)
  createDir(outDir)
  let t0 = epochTime()
  let log = open(outDir / "log.csv", fmAppend)
  if log.getFileSize == 0: log.writeLine "time_s,programs,finding_id,signature"
  var sigs: Table[string, int]
  for k in 0 ..< count:
    let s = seed + k
    var p: seq[N]
    var exp: seq[string]
    try: (p, exp) = generate(s)
    except CatchableError as e:
      echo &"seed {s}: GENERATOR BUG: {e.msg}"
      continue
    let res = check(p, exp)
    echo &"seed {s}: " & (if res.len == 0: "ok" else: $res.len & " problem(s)")
    for (sig, detail) in res:
      let new = sig notin sigs
      if new: sigs[sig] = sigs.len + 1
      let id = sigs[sig]
      log.writeLine &"{epochTime() - t0:.0f},{k + 1},{id},{sig.replace(',', ';')}"
      log.flushFile
      echo &"  f{id:02} " & (if new: "NEW " else: "") & sig
      if not new: continue
      let d = outDir / &"f{id:02}_s{s}"
      createDir d
      writeFile(d / "prog.nim", render(p))
      writeFile(d / "expected.txt", exp.join("\n") & "\n")
      writeFile(d / "detail.txt", sig & "\n" & detail)
      if doReduce:
        let m = reduce(generate(s)[0], sig)
        writeFile(d / "min.nim", render(m))
        writeFile(d / "min.expected", model(m).join("\n") & "\n")
        echo &"  reduced with {tests} tests to {render(m).countLines} lines: {d}/min.nim"
  var ru: Rusage
  discard getrusage(RUSAGE_CHILDREN, addr ru)
  let cpu = ru.ru_utime.tv_sec.int + ru.ru_stime.tv_sec.int + cpuTime().int
  log.writeLine &"# end: elapsed_s={epochTime() - t0:.0f} programs={count} distinct={sigs.len} cpu_s={cpu}"
  log.close
  echo &"{count} programs, {sigs.len} signatures, cpu {cpu}s -- {outDir}"

main()
