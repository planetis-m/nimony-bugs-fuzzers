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

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables]

type
  Kind = enum                  ## e: expressions, s: statements
    eLit, eVar, eAdd, eMul, eSub, eLt, eEq, eEven,
    sEcho, sEchoErr, sDecl, sAsgn, sCall, sIf, sCase, sWhile, sFor, sForIt,
    sBreak, sCont, sRet, sRaise, sReraise, sYield, sDefer, sTry,
    sClo, sCloSet, sSeq, sSeqAdd, sBox, sBoxSet, sIter, sFacRes,
    cLit, cVar, cFac,        ## closure sources: literal, variable, factory call
    dFac, dUnit              ## top level: factory proc, test proc `u<i>`

  Node = ref object            ## a program node; it both emits source and runs in the model
    kind: Kind
    name: string               ## declared or assigned variable, echo tag, routine name
    other: string              ## callee, iterator, error variable, factory param
    num: int                   ## literal, loop bound, callee kind (closure/seq/box), has finally, p0
    aux: int                   ## seq index of a call, p1
    args: seq[Node]            ## expressions
    bodies: seq[seq[Node]]     ## statement lists: what the reducer shrinks
    src: Node                  ## closure source; a factory's literal
    params: seq[string]        ## iterator params
    clo, guarded, cleanup, mayRaise: bool  ## iterator facts, see `forIter`

# ---- emitting ----------------------------------------------------------------

proc emitExpr(e: Node): string =
  template x(i): string = emitExpr(e.args[i])
  case e.kind
  of eLit: $e.num
  of eVar: e.name
  of eAdd: "((" & x(0) & " + " & x(1) & ") mod 997)"
  of eMul: "((" & x(0) & " * " & x(1) & ") mod 997)"
  of eSub: "((" & x(0) & " + 997 - " & x(1) & ") mod 997)"
  of eLt: x(0) & " < " & x(1)
  of eEq: x(0) & " == " & x(1)
  of eEven: x(0) & " mod 2 == 0"
  else: "?"

proc emit(s: Node; ind: int; o: var seq[string])

proc emit(l: seq[Node]; ind: int; o: var seq[string]) =
  if l.len == 0: o.add repeat("  ", ind) & "discard"
  for s in l: emit(s, ind, o)

const cloHead = "proc (Y: int): int {.closure, raises.} ="

proc emitSrc(pre: string; c: Node; ind: int; o: var seq[string]) =
  ## Emits closure source `c` after `pre` (`var x: CT = `, `s.add ` ...).
  let p = repeat("  ", ind)
  case c.kind
  of cLit:
    o.add p & pre & cloHead.replace("Y", c.name)
    o.add p & "  result = 0"
    emit(c.bodies[0], ind + 1, o)
  of cVar: o.add p & pre & c.name
  else: o.add p & pre & c.name & "(" & emitExpr(c.args[0]) & ")"

proc emit(s: Node; ind: int; o: var seq[string]) =
  let p = repeat("  ", ind)
  template ln(x: string) = o.add p & x
  template sub(i: int) = emit(s.bodies[i], ind + 1, o)
  case s.kind
  of sEcho: ln "echo \"" & s.name & " \", " & emitExpr(s.args[0])
  of sEchoErr: ln "echo \"" & s.name & " \", " & s.other
  of sDecl: ln "var " & s.name & " = " & emitExpr(s.args[0])
  of sAsgn: ln s.name & " = " & emitExpr(s.args[0])
  of sCall:
    let callee = [s.other, s.other & "[" & $s.aux & "]", s.other & ".f"][s.num]
    ln (if s.num == 1: "if " & s.other & ".len > " & $s.aux & ": " else: "") &
       (if s.name != "": s.name & " = " else: "discard ") & callee & "(" & emitExpr(s.args[0]) & ")"
  of sIf:
    ln "if " & emitExpr(s.args[0]) & ":"; sub 0
    if s.bodies[1].len > 0: ln "else:"; sub 1
  of sCase:
    ln "case (" & emitExpr(s.args[0]) & ") mod 3"
    ln "of 0:"; sub 0
    ln "of 1:"; sub 1
    ln "else:"; sub 2
  of sWhile:
    ln "var " & s.name & " = 0"
    ln "while " & s.name & " < " & $s.num & ":"
    ln "  inc " & s.name
    sub 0
  of sFor: ln "for " & s.name & " in 0 ..< " & $s.num & ":"; sub 0
  of sForIt:
    var args: seq[string]
    for a in s.args: args.add emitExpr(a)
    ln "for " & s.name & " in " & s.other & "(" & args.join(", ") & "):"; sub 0
  of sBreak: ln "break"
  of sCont: ln "continue"
  of sRet: ln "return"
  of sRaise: ln "raise " & s.name
  of sReraise: ln "raise"
  of sYield: ln "yield " & emitExpr(s.args[0])
  of sDefer: ln "defer:"; sub 0
  of sTry:
    ln "try:"; sub 0
    if s.name != "": ln "except ErrorCode as " & s.name & ":"; sub 1
    if s.num == 1: ln "finally:"; sub 2
  of sClo: emitSrc("var " & s.name & ": CT = ", s.src, ind, o)
  of sCloSet: emitSrc(s.name & " = ", s.src, ind, o)
  of sSeq: ln "var " & s.name & ": seq[CT] = @[]"
  of sSeqAdd: emitSrc(s.name & ".add ", s.src, ind, o)
  of sBox: emitSrc("var " & s.name & " = Box(f: ", s.src, ind, o); o[^1].add ")"
  of sBoxSet: emitSrc(s.name & ".f = ", s.src, ind, o)
  of sIter:
    var ps: seq[string]
    for a in s.params: ps.add a & ": int"
    ln "iterator " & s.name & "(" & ps.join(", ") & "): int {." &
       (if s.clo: "closure, " else: "") & "raises, sideEffect.} ="
    sub 0
  of dFac:
    ln "proc " & s.name & "(" & s.other & ": int): CT {.raises.} ="
    sub 0
    ln "  result = " & cloHead.replace("Y", s.src.name)
    ln "    result = 0"
    emit(s.src.bodies[0], ind + 2, o)
    for x in s.bodies[1]: emit(x, ind + 1, o)
  of dUnit: ln "proc " & s.name & "(p0, p1: int) {.raises.} ="; sub 0
  else: discard

proc render(p: seq[Node]): string =
  ## The whole program; the main part calls every unit and echoes the exception it raises.
  var o = @["import std/syncio", "", "type", "  CT = " & cloHead.replace("Y", "y")[0 .. ^3],
            "  Box = object", "    f: CT", ""]
  for d in p: emit(d, 0, o); o.add ""
  for d in p:
    if d.kind == dUnit:
      o.add ["try:", &"  {d.name}({d.num}, {d.aux})", "except ErrorCode as e:", &"  echo \"{d.name} exc \", e"]
  o.join("\n") & "\n"

# ---- the model ---------------------------------------------------------------

type
  ValKind = enum vNil, vInt, vClo, vSeq, vBox, vErr, vIter
  Val = object
    kind: ValKind
    num: int
    err: string                ## error code
    def: Node                  ## closure literal or iterator definition
    env: Scope                 ## the scope it was created in
    items: seq[Val]            ## seq elements; a box is a one-element seq
  Cell = ref object            ## a variable; closures capture the cell, i.e. by reference
    v: Val
  Scope = ref object
    vars: seq[(string, Cell)]
    up: Scope
  OnYield = proc (v: int)      ## the loop body a `yield` runs
  Fuel = object of CatchableError     ## step budget spent: may not terminate
  Invalid = object of CatchableError  ## not a valid program (common for reduced variants)
  # control flow travels as exceptions
  BreakX = object of CatchableError
  ContX = object of CatchableError
  RetX = object of CatchableError
  NimErr = object of CatchableError   ## a program `raise`; msg is the error code
  Escape = object of CatchableError  ## leaves loop `id` through its iterator
    id: int
    inner: ref CatchableError

var output: seq[string]        ## what the program echoes
var fuel, depth, loopIds: int  ## steps left, closure call depth, last `Escape` id
var iters, facs: Table[string, Node]  ## top-level iterators and factories

proc invalid(m: string) {.noreturn.} = raise newException(Invalid, m)
proc tick() =
  ## One step; raises `Fuel` on endless loops and runaway output.
  dec fuel
  if fuel < 0 or output.len > 4000: raise newException(Fuel, "")

proc lookup(sc: Scope; n: string): Cell =
  var s = sc
  while s != nil:
    for i in countdown(s.vars.high, 0):
      if s.vars[i][0] == n: return s.vars[i][1]
    s = s.up
  invalid "undeclared " & n

proc decl(sc: Scope; n: string; v: Val) = sc.vars.add (n, Cell(v: v))
proc intVal(x: int): Val = Val(kind: vInt, num: x)
proc asInt(c: Cell): int =
  if c.v.kind != vInt: invalid "not an int"
  c.v.num
proc setInt(sc: Scope; n: string; x: int) =
  let c = lookup(sc, n)
  discard asInt(c)             # assigning to a closure variable is invalid
  c.v = intVal(x)

proc eval(e: Node; sc: Scope): int =
  template x(i): int = eval(e.args[i], sc)
  case e.kind
  of eLit: e.num
  of eVar: asInt(lookup(sc, e.name))
  of eAdd: (x(0) + x(1)) mod 997
  of eMul: (x(0) * x(1)) mod 997
  of eSub: (x(0) + 997 - x(1)) mod 997
  of eLt: ord(x(0) < x(1))
  of eEq: ord(x(0) == x(1))
  of eEven: ord(x(0) mod 2 == 0)
  else: invalid "not an expression"

proc runList(l: seq[Node]; sc: Scope; y: OnYield)

proc callClo(c: Val; arg: int): int =
  tick()
  inc depth
  if depth > 60: raise newException(Fuel, "")
  try:
    let s = Scope(up: c.env)
    s.decl(c.def.name, intVal(arg))
    s.decl("result", intVal(0))
    try: runList(c.def.bodies[0], s, nil)
    except RetX: discard
    result = asInt(lookup(s, "result"))
  finally: dec depth

proc evalSrc(c: Node; sc: Scope): Val =
  ## The closure a source denotes; a factory source runs the factory.
  case c.kind
  of cLit: Val(kind: vClo, def: c, env: sc)
  of cVar:
    let v = lookup(sc, c.name).v
    if v.kind != vClo: invalid "not a closure"
    v
  else:
    let f = facs.getOrDefault(c.name)
    if f == nil: invalid "no factory"
    let a = eval(c.args[0], sc)
    tick()
    let s = Scope()
    s.decl(f.other, intVal(a))
    s.decl("result", Val())
    # one list: a `defer` in the prologue covers the rest of the proc
    runList(f.bodies[0] & @[Node(kind: sFacRes, src: f.src)] & f.bodies[1], s, nil)
    lookup(s, "result").v

proc store(sc: Scope; n: string; k: ValKind; v: Val) =
  ## Sets closure variable `n`, appends to seq `n` or replaces the closure in box `n`.
  let c = lookup(sc, n)
  if c.v.kind != k: invalid "wrong kind: " & n
  case k
  of vSeq: c.v.items.add v
  of vBox: c.v.items[0] = v
  else: c.v = v

proc runBody(l: seq[Node]; sc: Scope; y: OnYield): bool =
  ## Runs a loop body; true on `break`.
  try: runList(l, sc, y)
  except ContX: discard
  except BreakX: result = true

proc run(s: Node; sc: Scope; y: OnYield) =
  case s.kind
  of sEcho: output.add s.name & " " & $eval(s.args[0], sc)
  of sEchoErr:
    let v = lookup(sc, s.other).v
    if v.kind != vErr: invalid "not an error"
    output.add s.name & " " & v.err
  of sDecl: sc.decl(s.name, intVal(eval(s.args[0], sc)))
  of sAsgn: sc.setInt(s.name, eval(s.args[0], sc))
  of sCall:
    let c = lookup(sc, s.other).v
    var f = c
    if s.num > 0:
      if c.kind != [vNil, vSeq, vBox][s.num]: invalid "not a seq/box"
      if s.num == 1 and s.aux >= c.items.len: return
      f = c.items[if s.num == 1: s.aux else: 0]
    if f.kind != vClo: invalid "not a closure"
    let r = callClo(f, eval(s.args[0], sc))
    if s.name != "": sc.setInt(s.name, r)
  of sIf: runList(s.bodies[if eval(s.args[0], sc) != 0: 0 else: 1], Scope(up: sc), y)
  of sCase: runList(s.bodies[eval(s.args[0], sc) mod 3], Scope(up: sc), y)
  of sWhile:
    sc.decl(s.name, intVal(0))
    let c = lookup(sc, s.name)
    while c.v.num < s.num:
      tick()
      inc c.v.num
      if runBody(s.bodies[0], Scope(up: sc), y): break
  of sFor:
    for i in 0 ..< s.num:
      tick()
      let s2 = Scope(up: sc)
      s2.decl(s.name, intVal(i))
      if runBody(s.bodies[0], s2, y): break
  of sForIt:
    var d = iters.getOrDefault(s.other)  # else a local iterator, held in a variable
    var env: Scope = nil
    if d == nil:
      let v = lookup(sc, s.other).v
      if v.kind != vIter: invalid "no iterator " & s.other
      d = v.def
      env = v.env
    if d.params.len != s.args.len: invalid "arity"
    let isc = Scope(up: env)
    for j, p in d.params: isc.decl(p, intVal(eval(s.args[j], sc)))
    # The iterator runs with the loop body as its yield callback. Anything that
    # leaves the body is wrapped in an `Escape` so that unwinding runs the
    # iterator's finally/defer but not its except; this loop unwraps it.
    inc loopIds
    let id = loopIds
    let cb = proc (v: int) =
      tick()
      let s2 = Scope(up: sc)
      s2.decl(s.name, v.intVal)
      try: runList(s.bodies[0], s2, y)
      except ContX: discard
      except CatchableError as e: raise (ref Escape)(id: id, inner: e)
    try:
      try: runList(d.bodies[0], isc, cb)
      except RetX: discard
    except Escape as e:
      if e.id != id: raise
      if not (e.inner of BreakX): raise e.inner
  of sBreak: raise newException(BreakX, "")
  of sCont: raise newException(ContX, "")
  of sRet: raise newException(RetX, "")
  of sRaise: raise newException(NimErr, s.name)
  of sReraise:
    let v = lookup(sc, s.name).v
    if v.kind != vErr: invalid "reraise"
    raise newException(NimErr, v.err)
  of sYield:
    if y == nil: invalid "yield outside of an iterator"
    y(eval(s.args[0], sc))
  of sTry:
    try:
      try: runList(s.bodies[0], Scope(up: sc), y)
      except NimErr as e:      # never an Escape or break/continue/return
        if s.name == "": raise
        let s2 = Scope(up: sc)
        s2.decl(s.name, Val(kind: vErr, err: e.msg))
        runList(s.bodies[1], s2, y)
    finally:
      if s.num == 1: runList(s.bodies[2], Scope(up: sc), nil)
  of sClo: sc.decl(s.name, evalSrc(s.src, sc))
  of sCloSet: sc.store(s.name, vClo, evalSrc(s.src, sc))
  of sSeq: sc.decl(s.name, Val(kind: vSeq))
  of sSeqAdd: sc.store(s.name, vSeq, evalSrc(s.src, sc))
  of sBox: sc.decl(s.name, Val(kind: vBox, items: @[evalSrc(s.src, sc)]))
  of sBoxSet: sc.store(s.name, vBox, evalSrc(s.src, sc))
  of sIter: sc.decl(s.name, Val(kind: vIter, def: s, env: sc))
  of sFacRes: lookup(sc, "result").v = Val(kind: vClo, def: s.src, env: sc)
  else: invalid "not a statement"

proc runList(l: seq[Node]; sc: Scope; y: OnYield) =
  for i, s in l:
    if s.kind == sDefer:       # = try/finally around the rest of the list
      try: runList(l[i+1 .. ^1], sc, y)
      finally: runList(s.bodies[0], Scope(up: sc), nil)
      return
    tick()
    run(s, sc, y)

proc model(p: seq[Node]): seq[string] =
  ## Expected output; raises Invalid or Fuel.
  output = @[]
  fuel = 30000
  depth = 0
  iters.clear
  facs.clear
  for d in p:
    if d.kind == sIter: iters[d.name] = d
    if d.kind == dFac: facs[d.name] = d
  for d in p:
    if d.kind != dUnit: continue
    let sc = Scope()
    sc.decl("p0", intVal(d.num))
    sc.decl("p1", intVal(d.aux))
    try: runList(d.bodies[0], sc, nil)
    except RetX: discard
    except NimErr as e: output.add d.name & " exc " & e.msg
    except BreakX, ContX: invalid "stray break"
  output

# ---- the generator -----------------------------------------------------------

type
  SymKind = enum gInt, gClo, gSeq, gBox, gErr
  Sym = object                 ## a variable the generator may use
    name: string
    kind: SymKind
    depth: int                 ## loop depth of the declaration
    capDepth: int              ## a closure's capture limit: deepest loop it captures from
    readonly: bool
  Ctx = object                 ## where the next statement goes
    routine: string            ## unit clo iter citer fac
    vars: seq[Sym]
    iters, facs: seq[Node]
    depth, nest: int           ## loop depth, statement nesting
    inLoop, noRaise, canYield: bool
    exceptGuard: bool          ## inside a `try` with `except`
    pure: bool                 ## defer/finally body: only echo and assignment
    iter: Node                 ## the iterator being generated

var rng: Rand
var counter: int               ## for fresh names
var small: bool
var avoid = ""

proc fresh(p: string): string = inc counter; p & $counter
proc chance(p: float): bool = rng.rand(1.0) < p
proc rnd(a, b: int): int = rng.rand(a..b)
proc newCtx(routine: string; vars: seq[Sym]; its, fs: seq[Node]): Ctx =
  Ctx(routine: routine, vars: vars, iters: its, facs: fs, canYield: routine in ["iter", "citer"])
proc child(c: Ctx): Ctx = (result = c; inc result.nest)
proc loopCtx(c: Ctx): Ctx = (result = child(c); inc result.depth; result.inLoop = true)
proc pureCtx(c: Ctx): Ctx = (result = child(c); result.pure = true; result.canYield = false)
proc op(k: Kind; a: varargs[Node]): Node = Node(kind: k, args: @a)
proc lit(x: int): Node = Node(kind: eLit, num: x)
proc sym(n: string; k = gInt; depth = 0; readonly = false; capDepth = -1): Sym =
  Sym(name: n, kind: k, depth: depth, readonly: readonly, capDepth: capDepth)

proc varsOf(c: Ctx; k: SymKind; writable = false): seq[Sym] =
  ## The variables of kind `k` in scope; only assignable ones if `writable`.
  for v in c.vars:
    if v.kind == k and not (writable and v.readonly): result.add v

proc expr(c: Ctx; d = 2): Node =
  let vs = c.varsOf(gInt)
  if d <= 0 or chance(0.35):
    if vs.len > 0 and chance(0.7): return Node(kind: eVar, name: rng.sample(vs).name)
    return lit(rnd(0, 12))
  op(rng.sample([eAdd, eAdd, eMul, eSub]), expr(c, d - 1), expr(c, d - 1))

proc cond(c: Ctx): Node =
  case rng.sample([eLt, eEq, eEven, eLt])
  of eEven: op(eEven, expr(c, 1))
  of eEq: op(eEq, expr(c, 1), lit(rnd(0, 6)))
  else: op(eLt, expr(c, 1), expr(c, 1))

proc echoStmt(c: Ctx): Node =
  let errs = c.varsOf(gErr)
  if errs.len > 0 and chance(0.3): Node(kind: sEchoErr, name: fresh("t"), other: rng.sample(errs).name)
  else: Node(kind: sEcho, name: fresh("t"), args: @[expr(c)])

proc captures(c: Ctx; limit: int): seq[Sym] =
  ## What a closure created in `c` may see: captured values are read-only.
  for v in c.vars:
    if v.kind != gErr and v.name != "result" and v.depth <= limit:
      result.add sym(v.name, v.kind, -1, v.readonly or v.kind != gInt)

proc stmts(c: var Ctx; n: int): seq[Node]
proc body(c: Ctx): seq[Node] =
  var c = c
  stmts(c, rnd(1, if c.nest > 1: 2 else: 3))

proc cloLit(c: Ctx; limit: int): Node =
  ## A closure literal capturing only variables of loop depth <= limit.
  var vis = captures(c, limit)
  let p = fresh("y")
  vis.add [sym(p, readonly = true), sym("result")]
  var cc = newCtx("clo", vis, c.iters, c.facs)
  cc.nest = c.nest + 1
  var b = stmts(cc, rnd(1, 3))
  b.add Node(kind: sAsgn, name: "result", args: @[op(eAdd, Node(kind: eVar, name: "result"), expr(cc, 1))])
  Node(kind: cLit, name: p, bodies: @[b])

proc cloSrc(c: Ctx; limit: int; allowLit = true): Node =
  ## A closure source that captures nothing deeper than loop depth `limit`, or nil.
  var opts: seq[Kind]
  if allowLit and c.nest < 5: opts.add [cLit, cLit]
  var cvs: seq[Sym]
  for v in c.varsOf(gClo):
    if v.capDepth <= limit: cvs.add v
  if cvs.len > 0: opts.add cVar
  if c.facs.len > 0 and not c.noRaise: opts.add cFac
  if opts.len == 0: return nil
  case rng.sample(opts)
  of cLit: cloLit(c, limit)
  of cVar: Node(kind: cVar, name: rng.sample(cvs).name)
  else: Node(kind: cFac, name: rng.sample(c.facs).name, args: @[expr(c, 1)])

proc cloDecl(c: var Ctx): Node =
  ## Declares a closure variable or reassigns one.
  let n = fresh("c")
  let own = c.varsOf(gClo, writable = true)
  if own.len > 0 and chance(0.3):
    let v = rng.sample(own)
    let src = cloSrc(c, min(v.capDepth, c.depth))
    if src != nil: return Node(kind: sCloSet, name: v.name, src: src)
  let mc = rnd(-1, c.depth)
  let src = cloSrc(c, mc)
  if src == nil: return echoStmt(c)
  c.vars.add sym(n, gClo, c.depth, capDepth = mc)
  Node(kind: sClo, name: n, src: src)

proc walk(l: seq[Node]; res: var seq[Node]) =
  ## Every statement in `l`, nested ones and closure literals' included.
  for s in l:
    res.add s
    for k in s.bodies: walk(k, res)
    if s.src != nil and s.src.kind == cLit: walk(s.src.bodies[0], res)

proc find(its: seq[Node]; n: string): Node =
  for d in its:
    if d.name == n: return d

proc hasCleanup(l, its: seq[Node]): bool =
  var all: seq[Node]
  walk(l, all)
  for s in all:
    if s.kind == sDefer or (s.kind == sTry and s.num == 1): return true
    if s.kind == sForIt and its.find(s.other) != nil and its.find(s.other).cleanup: return true

proc mayRaise(l, its: seq[Node]): bool =
  ## Conservative: any call, raise, factory call or loop over a raising iterator.
  var all: seq[Node]
  walk(l, all)
  for s in all:
    if s.kind in {sRaise, sReraise, sCall}: return true
    if s.kind in {sClo, sCloSet, sBox, sSeqAdd, sBoxSet} and s.src.kind == cFac: return true
    if s.kind == sForIt and (its.find(s.other) == nil or its.find(s.other).mayRaise): return true

proc iterDef(name: string; cl: bool; outer: seq[Sym]; its, fs: seq[Node]; nest = 0): Node =
  ## An inline or (`cl`) closure iterator with 0-2 params that sees `outer`.
  result = Node(kind: sIter, name: name, clo: cl)
  var vs = outer
  for i in 0 ..< rnd(0, 2):
    result.params.add fresh("a")
    vs.add sym(result.params[^1], readonly = true)
  var c = newCtx(if cl: "citer" else: "iter", vs, its, fs)
  c.iter = result
  c.nest = nest
  var b = stmts(c, rnd(2, 5))
  var yields = false
  for s in b: yields = yields or s.kind == sYield
  if not yields: b.add Node(kind: sYield, args: @[expr(c)])
  result.bodies = @[b]
  result.cleanup = hasCleanup(b, its)
  result.mayRaise = mayRaise(b, its)

proc forIter(c: Ctx; d: Node): Node =
  ## A loop over `d`, or over a random iterator in scope if `d` is nil.
  var d = d
  if d == nil:
    var its: seq[Node]
    for d in c.iters:
      if not (c.noRaise and d.mayRaise): its.add d
    if its.len == 0: return echoStmt(c)
    d = rng.sample(its)
  elif c.noRaise and d.mayRaise: return echoStmt(c)
  let v = fresh("x")
  var lc = loopCtx(c)
  lc.vars.add sym(v, depth = lc.depth, readonly = true)
  # an inlined iterator's except would catch the body's raise, unlike our `Escape`
  if d.guarded: (lc.noRaise = true; lc.exceptGuard = true)
  # the body is inside the iterator's defer/finally scopes
  if c.routine == "citer" and d.cleanup: lc.canYield = false
  var args: seq[Node]
  for p in d.params: args.add expr(c, 1)
  Node(kind: sForIt, name: v, other: d.name, args: args, bodies: @[body(lc)])

proc callees(c: Ctx): seq[(int, string)] =
  ## (0 closure, 1 seq, 2 box; name) for every callable variable.
  for v in c.vars:
    case v.kind
    of gClo: result.add (0, v.name)
    of gSeq: result.add (1, v.name)
    of gBox: result.add (2, v.name)
    else: discard

proc stmt(c: var Ctx): seq[Node] =
  ## One random statement (two with `--avoid:unused-local-iter`).
  template one(x: Node) = return @[x]
  template maybeIf(x: Node; p = 0.7) = one(if chance(p): Node(kind: sIf, args: @[cond(c)], bodies: @[@[x], @[]]) else: x)
  let ints = c.varsOf(gInt, writable = true)
  if c.pure:
    if ints.len > 0 and chance(0.3): one Node(kind: sAsgn, name: rng.sample(ints).name, args: @[expr(c)])
    one Node(kind: sEcho, name: fresh("t"), args: @[expr(c)])
  var w = @[("echo", 5), ("decl", 3), ("assign", if ints.len > 0: 3 else: 0)]
  if c.nest < (if small: 2 else: 3):
    w.add [("if", 3), ("case", 1), ("while", 1), ("for", 1), ("foriter", if c.iters.len > 0: 5 else: 0),
           ("try", 2), ("defer", if c.routine == "citer": 0 else: 2), ("clodecl", 3), ("seq", 1),
           ("box", 1), ("localiter", 1)]
  if not c.noRaise: w.add [("call", if callees(c).len > 0: 4 else: 0), ("raise", 1)]
  if c.inLoop: w.add [("break", 1), ("continue", 1)]
  if c.routine != "fac": w.add ("return", 1)
  if c.canYield: w.add ("yield", 6)
  var total = 0
  for (_, x) in w: total += x
  var p = rng.rand(total - 1)
  var key = ""
  for (k, x) in w:
    if p < x: (key = k; break)
    p -= x
  case key
  of "echo": one echoStmt(c)
  of "decl":
    let n = fresh("v")
    let e = expr(c)
    c.vars.add sym(n, depth = c.depth)
    one Node(kind: sDecl, name: n, args: @[e])
  of "assign": one Node(kind: sAsgn, name: rng.sample(ints).name, args: @[expr(c)])
  of "if":
    let e = cond(c)
    let a = body(child(c))
    one Node(kind: sIf, args: @[e], bodies: @[a, if chance(0.5): body(child(c)) else: newSeq[Node]()])
  of "case":
    let e = expr(c, 1)
    one Node(kind: sCase, args: @[e], bodies: @[body(child(c)), body(child(c)), body(child(c))])
  of "while":
    let n = fresh("w")
    c.vars.add sym(n, depth = c.depth, readonly = true)
    one Node(kind: sWhile, name: n, num: rnd(1, 4), bodies: @[body(loopCtx(c))])
  of "for":
    let v = fresh("i")
    var lc = loopCtx(c)
    lc.vars.add sym(v, depth = lc.depth, readonly = true)
    one Node(kind: sFor, name: v, num: rnd(0, 4), bodies: @[body(lc)])
  of "foriter": one forIter(c, nil)
  of "try":
    let hasExc = chance(0.75)
    let hasFin = not hasExc or chance(0.5)
    var bc = child(c)
    bc.exceptGuard = bc.exceptGuard or hasExc
    if hasFin and c.routine == "citer": bc.canYield = false
    let bd = body(bc)
    var en = ""
    var h, f: seq[Node]
    if hasExc:
      en = fresh("e")
      var hc = child(c)
      if hasFin and c.routine == "citer": hc.canYield = false
      hc.vars.add sym(en, gErr, c.depth)
      h = body(hc)
      if not c.noRaise and chance(0.2): h.add Node(kind: sReraise, name: en)
    if hasFin: f = body(pureCtx(c))
    one Node(kind: sTry, name: en, num: ord(hasFin), bodies: @[bd, h, f])
  of "defer": one Node(kind: sDefer, bodies: @[body(pureCtx(c))])
  of "clodecl": one cloDecl(c)
  of "seq":
    let ss = c.varsOf(gSeq, writable = true)
    if ss.len > 0 and chance(0.7):
      let v = rng.sample(ss)
      let src = cloSrc(c, v.depth)
      if src != nil: one Node(kind: sSeqAdd, name: v.name, src: src)
    let n = fresh("s")
    c.vars.add sym(n, gSeq, c.depth)
    one Node(kind: sSeq, name: n)
  of "box":
    let bs = c.varsOf(gBox, writable = true)
    if bs.len > 0 and chance(0.5):
      let v = rng.sample(bs)
      let src = cloSrc(c, v.depth)
      if src != nil: one Node(kind: sBoxSet, name: v.name, src: src)
    let src = cloSrc(c, c.depth, allowLit = false)
    if src == nil: one cloDecl(c)
    let n = fresh("b")
    c.vars.add sym(n, gBox, c.depth)
    one Node(kind: sBox, name: n, src: src)
  of "localiter":
    let cl = chance(0.5) and not ("citer-in-citer" in avoid and c.routine == "citer")
    # a local INLINE iterator may not touch the enclosing routine's locals
    let d = iterDef(fresh("li"), cl, if cl: captures(c, high(int)) else: newSeq[Sym](), c.iters, c.facs, c.nest + 1)
    c.iters.add d
    if "unused-local-iter" in avoid: return @[d, forIter(c, d)]  # use it at once
    one d
  of "call":
    let (ck, cn) = rng.sample(callees(c))
    let tgt = if ints.len > 0 and chance(0.75): rng.sample(ints).name else: ""
    one Node(kind: sCall, name: tgt, other: cn, num: ck, aux: rnd(0, 2), args: @[expr(c, 1)])
  of "raise": maybeIf Node(kind: sRaise, name: rng.sample(["SyntaxError", "IOError", "RangeError", "ValueError"]))
  of "break": maybeIf Node(kind: sBreak)
  of "continue": maybeIf Node(kind: sCont)
  of "return": maybeIf(Node(kind: sRet), 2.0)  # always conditional
  else:
    if c.exceptGuard and c.iter != nil and not c.iter.clo: c.iter.guarded = true
    one Node(kind: sYield, args: @[expr(c)])

proc stmts(c: var Ctx; n: int): seq[Node] =
  for i in 0 ..< n: result.add stmt(c)

proc factory(name: string; fs: seq[Node]): Node =
  ## `proc mk(a): CT`: prologue, `result = <closure literal>`, epilogue.
  let p = fresh("a")
  var c = newCtx("fac", @[sym(p, readonly = true)], @[], fs)
  c.noRaise = true           # `result` is not set yet: a raise would leave it unproven
  let pre = stmts(c, rnd(1, 3))
  c.noRaise = false
  let clo = cloLit(c, 0)
  Node(kind: dFac, name: name, other: p, src: clo, bodies: @[pre, stmts(c, rnd(0, 2))])

proc generate(seed: int): (seq[Node], seq[string]) =
  ## A program and its expected output; retries sub-seeds until it terminates.
  for sub in 0 ..< 50:
    rng = initRand(seed * 1000 + sub + 1)
    counter = 0
    small = rng.rand(1.0) < 0.6  # most programs are small: one crash hides less
    var p: seq[Node]
    for u in 0 ..< (if small: 1 else: rnd(1, 3)):
      let un = "u" & $u
      var its, fs: seq[Node]
      for j in 0 ..< rnd(0, if small: 1 else: 3):
        fs.add factory(un & "_mk" & $j, fs)
        p.add fs[^1]
      for j in 0 ..< rnd(1, if small: 2 else: 3):
        its.add iterDef(un & "_it" & $j, chance(0.3), @[], its, fs)
        p.add its[^1]
      var c = newCtx("unit", @[sym("p0", readonly = true), sym("p1", readonly = true)], its, fs)
      let b = stmts(c, if small: rnd(3, 5) else: rnd(4, 8))
      p.add Node(kind: dUnit, name: un, bodies: @[b], num: rnd(0, 9), aux: rnd(0, 9))
    try: return (p, model(p))
    except Fuel: discard
  raise newException(Fuel, "no terminating program for seed " & $seed)

# ---- running -----------------------------------------------------------------

var nimony = "/home/ageralis/Projects/nimony/bin/nimony"
var work = ""

proc normalize(s: string): string =
  ## Error line without paths and generated names: `c12.0` -> `ID.N`.
  var words = s.strip.split(' ')
  for w in words.mitems:
    let a = w.find('/')
    let b = w.rfind('/')
    if a < b: w.delete(a .. b)
  let t = words.join(" ")
  var i = 0
  while i < t.len and result.len < 160:
    if t[i] in IdentChars:
      var j = i
      while j < t.len and t[j] in IdentChars: inc j
      let tok = t[i ..< j]
      var digits = 0
      for ch in tok:
        if ch in Digits: inc digits
      result.add(if digits == tok.len: "N" elif digits > 0: "ID" else: tok)
      i = j
    else:
      result.add t[i]
      inc i

proc compileSig(o: string): string =
  ## The first line matching the most telling pattern, normalized.
  for pat in ["[Bug]", "Error: unhandled exception: ", "SIGSEGV", "Assertion", "error: ", "Error: "]:
    for l in o.splitLines:
      let p = l.find(pat)
      if p >= 0: return normalize(l.substr(p))
  let t = o.strip
  "failed:" & normalize(t.substr(t.rfind(Newlines) + 1))   # its last line

const Exe = when defined(windows): ".exe" else: ""   # executable suffix

proc run(cmd: string; secs: int; dir = ""; errFile = ""): (string, int) =
  ## `cmd` (one command) through the shell with stdin empty and its output captured (stderr
  ## too, unless `errFile`); killed after `secs` s, then exit code 124 as with
  ## timeout(1). Output goes to a file: a full pipe would stall the wait.
  let f = getTempDir() / "fz" & $getCurrentProcessId() & ".out"
  let null = when defined(windows): "NUL" else: "/dev/null"
  var line = cmd & " <" & null & " >" & quoteShell(f) &
             (if errFile == "": " 2>&1" else: " 2>" & quoteShell(errFile))
  when defined(windows): line = "cmd /s /c \"" & line & "\""
  let t = epochTime()
  let p = startProcess(line, dir, options = {poEvalCommand, poParentStreams})
  result[1] = p.waitForExit(secs * 1000)
  if p.running:
    p.kill
    discard p.waitForExit
  if epochTime() - t >= secs.float: result[1] = 124
  p.close
  result[0] = readFile(f)

proc build(src, backend: string): (string, string) =
  ## (executable or "", compiler output); the nimcache is kept between programs.
  let nc = work / backend
  for f in walkDirRec(nc):
    if f.extractFilename == "prog" & Exe: removeFile f
  let (o, rc) = run(&"{nimony.quoteShell} {backend} --nimcache:{nc.quoteShell} {src.quoteShell}", 300, work)
  if rc == 124: return ("", "compile-timeout")
  if rc == 0:
    for f in walkDirRec(nc):
      if f.extractFilename == "prog" & Exe: return (f, o)
  ("", o)

proc check(p: seq[Node]; expected: seq[string]; want = ""): seq[(string, string)] =
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
    let (text, rc) = run(exe.quoteShell, 15)
    var got = text.splitLines
    if got.len > 0 and got[^1] == "": got.setLen(got.len - 1)
    if rc == 124: result.add (b & ":run-timeout", text)
    elif rc != 0: result.add (&"{b}:exit{rc}:" & normalize(if got.len > 0: got[^1] else: ""), text)
    elif got != expected:
      var i = 0
      while i < min(got.len, expected.len) and got[i] == expected[i]: inc i
      let e = if i < expected.len: expected[i] else: "<eof>"
      let g = if i < got.len: got[i] else: "<eof>"
      result.add (b & ":mismatch", &"line {i+1}: expected {e} got {g}\n{text}")

# ---- reduction ---------------------------------------------------------------

var prog: seq[Node]            ## the program being reduced
var target: string             ## the signature it must keep
var tests = 0                  ## compile tests used in this reduction
var budget = 100               ## and allowed

proc fails(): bool =
  ## Whether `prog` is still a valid program and still shows `target`.
  if tests >= budget: return false
  var exp: seq[string]
  try: exp = model(prog)
  except CatchableError: return false
  inc tests
  for (sig, _) in check(prog, exp, target):
    if sig == target: return true

proc shrink(l: var seq[Node]): bool =
  ## Delete halves, quarters, ... single statements while the failure persists;
  ## then recurse into the remaining statements' bodies.
  var chunk = max(1, l.len div 2)
  while chunk >= 1 and l.len > 0:
    var i = 0
    while i < l.len:
      let stop = min(i + chunk, l.len)
      let saved = l[i ..< stop]
      for _ in i ..< stop: l.delete(i)
      if fails(): result = true
      else:
        for j, s in saved: l.insert(s, i + j)
        i += chunk
    chunk = chunk div 2
  for s in l:
    for j in 0 ..< s.bodies.len:
      if shrink(s.bodies[j]): result = true
    if s.src != nil and s.src.kind == cLit and shrink(s.src.bodies[0]): result = true

proc reduce(p: seq[Node]; sig: string): seq[Node] =
  prog = p
  target = sig
  tests = 0
  for round in 0 ..< 5:
    if not shrink(prog): break
  prog

# ---- driver ------------------------------------------------------------------

proc main() =
  var seed = 1
  var count = 10
  var minutes = 0.0
  var outDir = getAppDir() / "out"
  var doReduce = true
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "minutes": minutes = parseFloat(val)
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
    if minutes > 0 and epochTime() - t0 > minutes * 60:   # time budget used up
      count = k   # programs actually run, for the totals below
      break
    let s = seed + k
    var p: seq[Node]
    var expected: seq[string]
    try: (p, expected) = generate(s)
    except CatchableError as e:
      echo &"seed {s}: GENERATOR BUG: {e.msg}"
      continue
    let problems = check(p, expected)
    echo &"seed {s}: " & (if problems.len == 0: "ok" else: $problems.len & " problem(s)")
    for (sig, detail) in problems:
      let new = sig notin sigs
      if new: sigs[sig] = sigs.len + 1
      let id = sigs[sig]
      log.writeLine &"{epochTime() - t0:.0f},{k + 1},{id},{sig.replace(',', ';')}"
      log.flushFile
      echo &"  f{id:02} " & (if new: "NEW " else: "") & sig
      if not new: continue
      let dir = outDir / &"f{id:02}_s{s}"
      createDir dir
      writeFile(dir / "prog.nim", render(p))
      writeFile(dir / "expected.txt", expected.join("\n") & "\n")
      writeFile(dir / "detail.txt", sig & "\n" & detail)
      if doReduce:
        let m = reduce(generate(s)[0], sig)
        writeFile(dir / "min.nim", render(m))
        writeFile(dir / "min.expected", model(m).join("\n") & "\n")
        echo &"  reduced with {tests} tests to {render(m).countLines} lines: {dir}/min.nim"
  log.writeLine &"# end: elapsed_s={epochTime() - t0:.0f} programs={count} distinct={sigs.len}"
  log.close
  echo &"{count} programs, {sigs.len} signatures -- {outDir}"

main()
