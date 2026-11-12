## Exception / control-flow lowering fuzzer for Nimony (desugar, xelim, eraiser).
##
## Generates random programs full of try/except/finally, defer, raise, bare
## re-raise, return/break/continue out of `try` and `finally`, labeled blocks,
## string `case`, if/case/try/block EXPRESSIONS and object construction with
## field defaults. Every program is a tree that is both rendered to Nim and
## interpreted here with Nim's semantics (an abrupt exit from a `finally`
## replaces whatever was pending), so the expected output is known exactly:
## the oracle is that trace, not another backend. Each program is built with
## `nimony c`, `nimony c --opt:speed` and `nimony n` and its output compared.
##
## Programs are UB-free: values are masked (`and 1023`), loops are bounded.
## Two exception domains: ErrorCode (`raise ValueError`, `{.raises.}`) or a
## `ref` hierarchy E1 > E2, E3 (`{.raises: E1.}`). Shapes that hit already
## reported bugs are off by default; `--allow:DIGITS` turns them back on:
## 1 raise as if/case-expression branch, 2 try-expression with ref exceptions,
## 3 defer in an expression branch, 4 raise in finally/defer, 5 jumps in finally
## (findings/01..05.md).
##
## A failure signature is `cfg:cfail:<error line>`, `cfg:mismatch`,
## `cfg:crash:<rc>` or `cfg:timeout`. The reducer deletes procs, statements,
## except arms and case branches in halving chunks, unwraps compound statements
## and shrinks expressions, re-interpreting every candidate, while the signature
## stays the same.
##
##   nim c -d:release -o:exc/excfuzz exc/excfuzz.nim
##   exc/excfuzz --seed:1000 --count:50       # 50 programs
##   exc/excfuzz --one:1234                   # print one program + its trace
##   exc/excfuzz --seed:1 --count:20 --allow:4 --budget:300
##
## Findings go to `--out:DIR` (default exc/out): `<seed>_<cfg>.nim`,
## `.min.nim` (reduced, with expected and actual output) and `log.csv`
## (time_s, programs, seed, signature). Parallelism: start several processes
## with different `--seed` ranges.

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables]

type
  Kind = enum
    eLit, eVar, eCall, eAdd, eIfx, eTryx, eBlkx, eLen, eStr,  # int expressions (eStr: only in O(b: ..))
    cAnd, cOr, cNot, cLt, cSeq,                                # conditions (evaluate to 0/1)
    sEcho, sEchoE, sAsgn, sSAsgn, sRaise, sReraise, sIf, sFor, sBlock, sBreak, sCont,
    sRet, sTry, sDefer, sCase, sLet, sObj,
    xBr, xProc, xProg
  Node = ref object
    ## One tree for expressions, statements, branches, procs and the program.
    kind: Kind
    name: string  ## variable, callee, echo token, label, exception (`E2:m3` or a code),
                  ## proc name, except-arm kind ("all", "ec", "E1"..), string `case` selector
    text: string  ## string literal, `for` label, `break` label as rendered, `as` name,
                  ## `let`/object variable; xProc: initial `s0`
    tag: string   ## except arm: the token it echoes; xProc: initial `s1`
    val: int      ## eLit value, `for` bound
    vals: seq[string]  ## `of` labels of a case branch; object fields set by sObj
    exprs: seq[Node]   ## operands; xBr: optional tail (expr or sRaise); sCase: int selector
    body: seq[Node]    ## statements; sIf: [then, else]; sCase: [of.., else];
                       ## sTry: [body, arms..]; sLet: [sIf/sCase/sTry] instead of exprs[0]
    fin: Node          ## sTry: the finally branch
  Ctx = object  ## generator context: what is in scope and what is allowed here
    ints, mut, strs, helpers: seq[string]
    loops: seq[(bool, string)]  ## (is a `for`, label), innermost last
    inHelper, inArm, inExpr, inDefer: bool
    noRaise, noJump: bool  ## inside a finally: avoid known bugs 4 and 5
  Jump = object of CatchableError  ## raise/break/continue/return in flight
    kind: Kind
    id: string  ## exception (sRaise) or label (sBreak)
    val: int    ## return value
  Overrun = object of CatchableError  ## program too slow or too chatty; generate another
  Env = ref object
    ints: Table[string, int]
    strs: Table[string, string]

const
  Codes = ["ValueError", "IOError", "OverflowError", "KeyError", "RangeError", "SyntaxError"]
  Strs = ["", "a", "ab", "abc", "abd", "abcd", "abce", "b", "ba", "bab", "xyz", "xy", "hello",
          "help", "helpme", "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaab", "Abc", "abc ",
          "zz", "z", "qwertyuiop", "qwertyuiopa", "0", "01", "10"]
  Cfgs = [("c", "c"), ("opt", "c --opt:speed"), ("n", "n")]

var
  rng: Rand
  refExc: bool   ## ref-exception domain (E1..E3) instead of ErrorCode
  tokens, names: int  ## counters for fresh echo tokens and identifiers
  allow = ""

# ---- generator ----------------------------------------------------------------

proc chance(p: float): bool = rng.rand(1.0) < p
proc token(prefix = "t"): string = inc tokens; prefix & $tokens
proc fresh(prefix: string): string = inc names; prefix & $names
proc node(k: Kind; e: varargs[Node]): Node = Node(kind: k, exprs: @e)
proc lit(v: int): Node = Node(kind: eLit, val: v)
proc randExc(): string =
  ## A ref exception carries a unique message (`E2:m7`) so the trace shows which raise was caught.
  if refExc: rng.sample(["E1", "E2", "E2", "E3", "E3"]) & ":" & token("m") else: rng.sample(Codes)

proc cond(c: Ctx; d: int): Node
proc stmts(c: Ctx; d, n: int): seq[Node]

proc expr(c: Ctx; d: int): Node =
  if d <= 0 or chance(0.3):
    return (if c.ints.len > 0 and chance(0.6): Node(kind: eVar, name: rng.sample(c.ints))
            else: lit(rng.rand(9)))
  let x = rng.rand(1.0)
  if x < 0.30 and c.helpers.len > 0: Node(kind: eCall, name: rng.sample(c.helpers), exprs: @[expr(c, d-1)])
  elif x < 0.45: node(eAdd, expr(c, d-1), expr(c, d-1))
  elif x < 0.58: node(eIfx, cond(c, d-1), expr(c, d-1), expr(c, d-1))
  elif x < 0.70 and not (refExc and '2' notin allow): node(eTryx, expr(c, d-1), expr(c, d-1))
  elif x < 0.80: Node(kind: eBlkx, name: token("b"), exprs: @[expr(c, d-1)])
  elif x < 0.88 and c.strs.len > 0: Node(kind: eLen, name: rng.sample(c.strs))
  else: node(eAdd, expr(c, d-1), lit(rng.rand(5)))

proc cond(c: Ctx; d: int): Node =
  let x = rng.rand(1.0)
  if d > 0 and x < 0.35: node(rng.sample([cAnd, cOr]), cond(c, d-1), cond(c, d-1))
  elif d > 0 and x < 0.42: node(cNot, cond(c, d-1))
  elif x < 0.5 and c.strs.len > 0: Node(kind: cSeq, name: rng.sample(c.strs), text: rng.sample(Strs))
  else: node(cLt, expr(c, d-1), expr(c, d-1))

proc branch(c: Ctx; d: int; mayRaise = true): Node =
  ## A branch of an expression: optional statements, then a value (or a raise).
  result = Node(kind: xBr)
  if chance(0.5):
    var s = c
    s.inExpr = true; s.loops = @[]; s.inArm = false
    result.body = stmts(s, d-1, rng.rand(1..2))
  result.exprs = @[if mayRaise and '1' in allow and chance(0.1): Node(kind: sRaise, name: randExc())
                   else: expr(c, 2)]

proc strBranches(mk: proc(): Node): seq[Node] =
  ## `of` branches of a string case, labels drawn without repetition.
  var pool = @Strs
  rng.shuffle(pool)
  for i in 0 ..< rng.rand(1 .. (if chance(0.3): 10 else: 3)):
    let k = min(rng.rand(1..3), pool.len)
    if k == 0: break
    let b = mk()
    b.vals = pool[0 ..< k]
    pool = pool[k .. ^1]
    result.add b
proc arms(mk: proc(): Node): seq[Node] =
  ## Except arms, each echoing its own token so the trace shows which one ran.
  var kinds: seq[string]
  if refExc:
    kinds = @["E1", "E2", "E3"]
    rng.shuffle(kinds)
    kinds.setLen rng.rand(0..3)
    if chance(0.3): kinds.add "all"
  elif chance(0.8): kinds = @[rng.sample(["ec", "all"])]
  for kd in kinds:
    let b = mk()
    b.name = kd
    b.text = if kd != "all" and chance(0.6): fresh("e") else: ""
    b.tag = token("x")
    result.add b

proc letValue(c: Ctx; d: int; s: Node) =
  ## The value of `let`: a plain expression or a multi-line if/case/try.
  let x = rng.rand(1.0)
  if x < 0.2: s.exprs = @[expr(c, 3)]
  elif x < 0.4: s.body = @[Node(kind: sIf, exprs: @[cond(c, 2)], body: @[branch(c, d), branch(c, d)])]
  elif x < 0.55:
    var vals = @[0, 1, 2, 3, 4, 5]
    rng.shuffle(vals)
    let n = Node(kind: sCase, exprs: @[expr(c, 2)])
    for i in 0 ..< rng.rand(1..3):
      let k = rng.rand(1..2)
      let b = branch(c, d)
      for v in vals[0 ..< k]: b.vals.add $v
      vals = vals[k .. ^1]
      n.body.add b
    n.body.add branch(c, d)
    s.body = @[n]
  elif (x < 0.7 and c.strs.len > 0) or (refExc and '2' notin allow):
    if c.strs.len == 0: s.exprs = @[expr(c, 3)]
    else:
      s.body = @[Node(kind: sCase, name: rng.sample(c.strs),
                      body: strBranches(proc(): Node = branch(c, d)) & branch(c, d))]
  else:
    let n = Node(kind: sTry, body: @[branch(c, d, false)] & arms(proc(): Node = branch(c, d)))
    if chance(0.4) or n.body.len == 1:
      var f = c
      f.inExpr = true; f.loops = @[]; f.inArm = false; f.inDefer = true
      n.fin = Node(kind: xBr, body: stmts(f, d-1, rng.rand(1..2)))
    s.body = @[n]

proc stmt(c: Ctx; d: int): Node =
  let x = rng.rand(1.0)
  let noJump = c.inDefer or c.inExpr or c.noJump
  if d <= 0 or x < 0.12: Node(kind: sEcho, name: token())
  elif x < 0.20: Node(kind: sEchoE, name: token(), exprs: @[expr(c, 3)])
  elif x < 0.25 and c.mut.len > 0: Node(kind: sAsgn, name: rng.sample(c.mut), exprs: @[expr(c, 3)])
  elif x < 0.28 and c.strs.len > 0 and not c.inDefer:
    Node(kind: sSAsgn, name: rng.sample(c.strs), text: rng.sample(Strs))
  elif x < 0.35 and not c.inDefer and not c.noRaise: Node(kind: sRaise, name: randExc())
  elif x < 0.37 and c.inArm and not c.inDefer: Node(kind: sReraise)
  elif x < 0.45:
    Node(kind: sIf, exprs: @[cond(c, 2)],
         body: @[Node(kind: xBr, body: stmts(c, d-1, rng.rand(1..3))),
                 Node(kind: xBr, body: stmts(c, d-1, rng.rand(0..2)))])
  elif x < 0.52:
    let iv = fresh("i")
    let id = fresh("L")
    var s = c
    s.ints.add iv; s.loops.add (true, id); s.inArm = false
    Node(kind: sFor, name: iv, text: id, val: rng.rand(3), body: stmts(s, d-1, rng.rand(1..4)))
  elif x < 0.56:
    let lab = fresh("B")
    var s = c
    s.loops.add (false, lab)
    Node(kind: sBlock, name: lab, body: stmts(s, d-1, rng.rand(1..3)))
  elif x < 0.62 and c.loops.len > 0 and not noJump:
    # Nim has no labeled `for`: its label stays internal and the break is bare, so
    # it is only chosen when the `for` is innermost; a block break names its label.
    let inner = c.loops[^1]
    var hasFor = false
    var blocks: seq[(bool, string)]
    for l in c.loops:
      if l[0]: hasFor = true
      else: blocks.add l
    if hasFor and chance(0.35): Node(kind: sCont)
    elif inner[0] and chance(0.5): Node(kind: sBreak, name: inner[1])
    elif blocks.len > 0:
      let b = rng.sample(blocks)[1]
      Node(kind: sBreak, name: b, text: b)
    else: Node(kind: sBreak, name: inner[1])  # only `for`s in scope
  elif x < 0.66 and not noJump:
    Node(kind: sRet, exprs: (if c.inHelper: @[expr(c, 2)] else: @[]))
  elif x < 0.78 and not c.inDefer:
    var b = c
    b.inArm = false
    var a = c
    a.inArm = true
    let n = Node(kind: sTry, body: @[Node(kind: xBr, body: stmts(b, d-1, rng.rand(1..4)))] &
                     arms(proc(): Node = Node(kind: xBr, body: stmts(a, d-1, rng.rand(0..2)))))
    if chance(0.5) or n.body.len == 1:  # a try needs an except or a finally
      # no helper calls in a finally: they may raise (bug 4)
      if '4' notin allow: b.helpers = @[]; b.noRaise = true
      if '5' notin allow: b.noJump = true
      n.fin = Node(kind: xBr, body: stmts(b, d-1, rng.rand(1..3)))
    n
  elif x < 0.83 and not c.inDefer and not (c.inExpr and '3' notin allow):
    var s = c
    s.inDefer = true; s.inArm = false
    if '4' notin allow: s.helpers = @[]
    Node(kind: sDefer, body: stmts(s, d-1, rng.rand(1..2)))
  elif x < 0.89 and c.strs.len > 0:
    Node(kind: sCase, name: rng.sample(c.strs),
         body: strBranches(proc(): Node = Node(kind: xBr, body: stmts(c, d-1, rng.rand(1..2)))) &
               Node(kind: xBr, body: stmts(c, d-1, rng.rand(0..2))))
  elif x < 0.95:
    let n = Node(kind: sLet, name: token(), text: fresh("l"))
    letValue(c, d-1, n)
    n
  else:
    var fs = @["a", "b", "c", "pk"]
    rng.shuffle(fs)
    fs.setLen rng.rand(0..3)
    let n = Node(kind: sObj, name: token(), text: fresh("o"))
    for f in ["a", "b", "c", "pk"]:  # in declaration order; unset fields keep their defaults
      if f in fs:
        n.vals.add f
        n.exprs.add(if f == "b": Node(kind: eStr, name: rng.sample(Strs[0..11])) else: expr(c, 2))
    n

proc stmts(c: Ctx; d, n: int): seq[Node] =
  for i in 0 ..< n: result.add stmt(c, d)

proc gen(seed: int): Node =
  ## Helpers `f<i>(x): int` (callable from later procs) and test procs `t<i>()`.
  rng = initRand(seed)
  refExc = chance(0.35)
  tokens = 0; names = 0
  result = Node(kind: xProg)
  var helpers: seq[string]
  for i in 0 ..< rng.rand(1..4):
    let c = Ctx(ints: @["x", "h"], mut: @["h"], helpers: helpers, inHelper: true)
    result.body.add Node(kind: xProc, name: "f" & $i, body: stmts(c, 2, rng.rand(1..3)), exprs: @[expr(c, 2)])
    helpers.add "f" & $i
  for i in 0 ..< rng.rand(2..5):
    let c = Ctx(ints: @["v0", "v1"], mut: @["v0", "v1"], strs: @["s0", "s1"], helpers: helpers)
    result.body.add Node(kind: xProc, name: "t" & $i, body: stmts(c, 3, rng.rand(2..5)),
                         text: rng.sample(Strs), tag: rng.sample(Strs))

# ---- rendering ------------------------------------------------------------------

proc quote(s: string): string = '"' & s & '"'
proc beforeColon(x: string): string =
  ## `E2:m3` -> `E2`, `c:cfail:..` -> `c`; all of `x` when it has no colon.
  let i = x.find(':')
  if i < 0: x else: x.substr(0, i - 1)
proc renderExc(x: string): string =
  ## `E2:m3` -> `E2(msg: "m3")`; an ErrorCode stays as it is.
  let i = x.find(':')
  if i < 0: x else: x[0 ..< i] & "(msg: " & quote(x[i+1 .. ^1]) & ")"

proc renderExpr(e: Node): string =
  template x(i: int): string = renderExpr(e.exprs[i])
  case e.kind
  of eLit: $e.val
  of eVar: e.name
  of eCall: e.name & "(" & x(0) & ")"
  of eAdd: "((" & x(0) & " + " & x(1) & ") and 1023)"
  of eIfx: "(if " & x(0) & ": " & x(1) & " else: " & x(2) & ")"
  of eTryx: "(try: " & x(0) & " except: " & x(1) & ")"
  of eBlkx: "(block: (echo " & quote(e.name) & "; " & x(0) & "))"
  of eLen: e.name & ".len"
  of eStr: quote(e.name)
  of cAnd: "(" & x(0) & " and " & x(1) & ")"
  of cOr: "(" & x(0) & " or " & x(1) & ")"
  of cNot: "(not " & x(0) & ")"
  of cLt: "(" & x(0) & " < " & x(1) & ")"
  of cSeq: "(" & e.name & " == " & quote(e.text) & ")"
  else: "?"

proc renderStmt(s: Node; indent: int; lines: var seq[string])

proc renderBody(b: Node; indent: int; lines: var seq[string]; addDiscard = true) =
  ## The statements of `b` and its tail; `discard` if empty and the context needs a statement.
  if b.body.len + b.exprs.len == 0 and addDiscard: lines.add spaces(indent) & "discard"
  for x in b.body: renderStmt(x, indent, lines)
  if b.exprs.len > 0:
    lines.add spaces(indent) & (if b.exprs[0].kind == sRaise: "raise " & renderExc(b.exprs[0].name)
                                else: renderExpr(b.exprs[0]))

proc renderStmt(s: Node; indent: int; lines: var seq[string]) =
  let pad = spaces(indent)
  case s.kind
  of sEcho: lines.add pad & "echo " & quote(s.name)
  of sEchoE: lines.add pad & "echo " & quote(s.name & " ") & " & $(" & renderExpr(s.exprs[0]) & ")"
  of sAsgn: lines.add pad & s.name & " = " & renderExpr(s.exprs[0])
  of sSAsgn: lines.add pad & s.name & " = " & quote(s.text)
  of sRaise: lines.add pad & "raise " & renderExc(s.name)
  of sReraise: lines.add pad & "raise"
  of sIf:
    lines.add pad & "if " & renderExpr(s.exprs[0]) & ":"
    renderBody(s.body[0], indent+2, lines)
    if s.body[1].body.len + s.body[1].exprs.len > 0:
      lines.add pad & "else:"
      renderBody(s.body[1], indent+2, lines)
  of sFor:
    lines.add pad & &"for {s.name} in 0..<{s.val}:"
    renderBody(s, indent+2, lines)
  of sBlock:
    lines.add pad & "block " & s.name & ":"
    renderBody(s, indent+2, lines)
  of sDefer:
    lines.add pad & "defer:"
    renderBody(s, indent+2, lines)
  of sBreak: lines.add pad & strip("break " & s.text)
  of sCont: lines.add pad & "continue"
  of sRet: lines.add pad & "return" & (if s.exprs.len > 0: " " & renderExpr(s.exprs[0]) else: "")
  of sTry:
    lines.add pad & "try:"
    renderBody(s.body[0], indent+2, lines)
    for a in s.body[1 .. ^1]:
      let head = case a.name
        of "all": "except"
        of "ec": "except ErrorCode"
        else: "except " & a.name
      lines.add pad & head & (if a.text != "": " as " & a.text else: "") & ":"
      lines.add pad & "  echo " & (if a.text == "": quote(a.tag)
                                   elif refExc: quote(a.tag & " ") & ", " & a.text & ".msg"
                                   else: quote(a.tag & " ") & ", " & a.text)
      renderBody(a, indent+2, lines, false)  # the echo above is already a statement
    if s.fin != nil:
      lines.add pad & "finally:"
      renderBody(s.fin, indent+2, lines)
  of sCase:
    lines.add pad & "case " & (if s.name != "": s.name else: renderExpr(s.exprs[0]))
    for b in s.body[0 .. ^2]:
      var vals: seq[string]
      for v in b.vals: vals.add(if s.name != "": quote(v) else: v)
      lines.add pad & "of " & vals.join(", ") & ":"
      renderBody(b, indent+2, lines)
    lines.add pad & "else:"
    renderBody(s.body[^1], indent+2, lines)
  of sLet:
    if s.exprs.len > 0: lines.add pad & "let " & s.text & " = " & renderExpr(s.exprs[0])
    else:
      # render the if/case/try as a statement, then glue `let x = ` onto its first line
      let k = lines.len
      renderStmt(s.body[0], indent+2, lines)
      lines[k] = pad & "let " & s.text & " = " & lines[k].strip
    lines.add pad & "echo " & quote(s.name & " ") & ", " & s.text
  of sObj:
    var fs: seq[string]
    for i, f in s.vals:
      fs.add(case f
        of "b": "b: " & quote(s.exprs[i].name)
        of "pk": "p: P(k: " & renderExpr(s.exprs[i]) & ")"
        else: f & ": " & renderExpr(s.exprs[i]))
    let n = s.text
    lines.add pad & "let " & n & " = O(" & fs.join(", ") & ")"
    lines.add pad & "echo " & quote(s.name & " ") & ", " &
              [n & ".a", n & ".b", n & ".c", n & ".p.k"].join(", \" \", ")
  else: discard

proc render(p: Node): string =
  var lines = @["import std/syncio", "", "type", "  E1 = ref object of Exception",
                "  E2 = ref object of E1", "  E3 = ref object of E1", "  P = object", "    k: int = 3",
                "  O = object", "    a: int = 5", "    b: string = \"xy\"", "    c: int", "    p: P", ""]
  let raises = if refExc: "{.raises: E1.}" else: "{.raises.}"
  for x in p.body:
    if x.name[0] == 'f':
      lines.add &"proc {x.name}(x: int): int {raises} ="
      lines.add "  var h = x"
      renderBody(Node(kind: xBr, body: x.body), 2, lines)
      lines.add "  return " & renderExpr(x.exprs[0])
    else:
      lines.add &"proc {x.name}() {raises} ="
      lines.add ["  var v0 = 1", "  var v1 = 2", "  var s0 = " & quote(x.text), "  var s1 = " & quote(x.tag)]
      renderBody(x, 2, lines)
    lines.add ""
  for x in p.body:
    if x.name[0] == 't':
      lines.add(if refExc: "try: " & x.name & "() except E1 as e: echo \"U \", e.msg"
                else: "try: " & x.name & "() except ErrorCode as e: echo \"U \", e")
  lines.join("\n") & "\n"

# ---- interpreter: the expected trace ----------------------------------------------
# Every abrupt exit (raise, break, continue, return) is a Nim exception `Jump`, so
# the host's own try/finally gives the propagation order for free.

var
  trace: seq[string]
  steps: int
  procs: Table[string, Node]

proc emit(s: string) =
  trace.add s
  if trace.len > 3000: raise newException(Overrun, "too much output")
proc tick() =
  inc steps
  if steps > 200_000: raise newException(Overrun, "too many steps")
proc jump(k: Kind; id = ""; val = 0) = raise (ref Jump)(kind: k, id: id, val: val)
proc msg(x: string): string = x.substr(x.rfind(':') + 1)  ## ref: the msg; ErrorCode: its name

proc execAll(xs: seq[Node]; env: Env; cur: string)
proc select(s: Node; env: Env; cur: string): int

proc call(name: string; arg: int): int =
  let h = procs[name]
  let env = Env()
  env.ints["x"] = arg; env.ints["h"] = arg
  try: execAll(h.body & Node(kind: sRet, exprs: h.exprs), env, "")  # the trailing return is in the scope of any defer
  except Jump as j:
    if j.kind != sRet: raise
    return j.val

proc eval(e: Node; env: Env): int =
  tick()
  template x(i: int): int = eval(e.exprs[i], env)
  case e.kind
  of eLit: e.val
  of eVar: env.ints[e.name]
  of eCall: call(e.name, x(0))
  of eAdd: (let a = x(0); (a + x(1)) and 1023)  # left operand first, as Nim does
  of eIfx: (if x(0) != 0: x(1) else: x(2))
  of eTryx: (try: x(0) except Jump: x(1))
  of eBlkx: (emit e.name; x(0))
  of eLen: env.strs[e.name].len
  of cAnd: ord(x(0) != 0 and x(1) != 0)
  of cOr: ord(x(0) != 0 or x(1) != 0)
  of cNot: ord(x(0) == 0)
  of cLt: (let a = x(0); ord(a < x(1)))
  of cSeq: ord(env.strs[e.name] == e.text)
  else: raise newException(ValueError, "not an expression")

proc evalBranch(b: Node; env: Env; cur: string): int =
  execAll(b.body, env, cur)
  if b.exprs.len == 0: 0
  elif b.exprs[0].kind == sRaise: (jump(sRaise, b.exprs[0].name); 0)
  else: eval(b.exprs[0], env)

proc evalTry(s: Node; env: Env; cur: string): int =
  ## `cur` is the exception a bare `raise` re-raises: the one the enclosing arm caught.
  var pending: ref Jump  # what leaves the try once the finally is done
  try: result = evalBranch(s.body[0], env, cur)
  except Jump as j:
    var arm: Node
    if j.kind == sRaise:
      for a in s.body[1 .. ^1]:
        # first matching arm wins; "ec" catches every ErrorCode, E1 every ref exception
        if a.name in ["all", "ec", "E1"] or a.name == beforeColon(j.id):
          arm = a
          break
    if arm == nil: pending = j  # break/continue/return pass through the arms
    else:
      try:
        emit arm.tag & (if arm.text != "": " " & msg(j.id) else: "")
        result = evalBranch(arm, env, j.id)
      except Jump as j2: pending = j2
  if s.fin != nil: execAll(s.fin.body, env, cur)  # a jump out of the finally replaces pending
  if pending != nil: raise pending

proc select(s: Node; env: Env; cur: string): int =
  ## Runs an if/case/try (statement or `let` value) and returns the chosen branch's value.
  case s.kind
  of sIf: evalBranch(s.body[if eval(s.exprs[0], env) != 0: 0 else: 1], env, cur)
  of sCase:
    let v = if s.name != "": env.strs[s.name] else: $eval(s.exprs[0], env)
    for b in s.body[0 .. ^2]:
      if v in b.vals: return evalBranch(b, env, cur)
    evalBranch(s.body[^1], env, cur)
  else: evalTry(s, env, cur)

proc exec(s: Node; env: Env; cur: string) =
  tick()
  case s.kind
  of sEcho: emit s.name
  of sEchoE: emit s.name & " " & $eval(s.exprs[0], env)
  of sAsgn: env.ints[s.name] = eval(s.exprs[0], env)
  of sSAsgn: env.strs[s.name] = s.text
  of sRaise: jump(sRaise, s.name)
  of sReraise: jump(sRaise, cur)
  of sIf, sCase, sTry: discard select(s, env, cur)
  of sFor:
    for i in 0 ..< s.val:
      env.ints[s.name] = i
      try: execAll(s.body, env, cur)
      except Jump as j:
        if j.kind == sCont: continue  # continue always targets the innermost `for`
        if j.kind == sBreak and j.id == s.text: break
        raise
  of sBlock:
    try: execAll(s.body, env, cur)
    except Jump as j:
      if j.kind != sBreak or j.id != s.name: raise
  of sBreak: jump(sBreak, s.name)
  of sCont: jump(sCont)
  of sRet: jump(sRet, val = (if s.exprs.len > 0: eval(s.exprs[0], env) else: 0))
  of sLet: emit s.name & " " & $(if s.exprs.len > 0: eval(s.exprs[0], env) else: select(s.body[0], env, cur))
  of sObj:
    var a = 5  # the field defaults declared in `render`
    var b = "xy"
    var c = 0
    var k = 3
    for i, f in s.vals:
      case f
      of "a": a = eval(s.exprs[i], env)
      of "b": b = s.exprs[i].name
      of "c": c = eval(s.exprs[i], env)
      else: k = eval(s.exprs[i], env)
    emit &"{s.name} {a} {b} {c} {k}"
  else: raise newException(ValueError, "not a statement")

proc execAll(xs: seq[Node]; env: Env; cur: string) =
  for i, s in xs:
    if s.kind == sDefer:  # the rest of the scope is the try body, the defer its finally
      var pending: ref Jump
      try: execAll(xs[i+1 .. ^1], env, cur)
      except Jump as j: pending = j
      execAll(s.body, env, cur)
      if pending != nil: raise pending
      return
    exec(s, env, cur)

proc expected(p: Node): string =
  ## The output the program must print; raises Overrun if it runs too long.
  trace.setLen 0
  steps = 0
  procs.clear
  for x in p.body: procs[x.name] = x
  for t in p.body:
    if t.name[0] != 't': continue
    let env = Env()
    env.ints["v0"] = 1; env.ints["v1"] = 2; env.strs["s0"] = t.text; env.strs["s1"] = t.tag
    try: execAll(t.body, env, "")
    except Jump as j:
      if j.kind == sRaise: emit "U " & msg(j.id)
  for t in trace: result.add t & "\n"

proc make(seed: int): Node =
  ## The first program from `seed` that terminates quietly enough.
  for salt in 0 .. 999:
    result = gen(seed * 1000 + salt)
    try:
      discard expected(result)
      return
    except Overrun: discard

# ---- oracle ---------------------------------------------------------------------

var
  nimony = getAppDir() / "../../nimony/bin/nimony"
  work = getAppDir() / "work"
  budget = 300
  actual = ""  ## output of the last program run

proc errKey(o: string): string =
  ## The first error line, paths dropped and numbers collapsed, so the reducer
  ## keeps chasing the same failure.
  var line = ""
  for x in o.splitLines:
    if "Error" in x or "error:" in x or "Bug" in x or "BUG" in x:
      line = x
      break
  if line == "":  # no error line: key on the last output line
    let t = o.strip
    line = if t.len == 0: "?" else: t.substr(t.rfind('\n') + 1)
  for w in line.splitWhitespace:
    for c in (if '/' in w: w.extractFilename else: w) & " ":
      if c notin Digits: result.add c
      elif result.len == 0 or result[^1] != 'N': result.add 'N'
  result = result.strip
  if result.len > 110: result.setLen 110

proc verdict(p: Node; cfg: string): string =
  ## "" when the backend agrees with the interpreter, else the failure signature.
  var exp = ""
  try: exp = expected(p)
  except CatchableError: return "INVALID"  # a reducer edit broke the program (e.g. undeclared var)
  let dir = work / cfg
  let nimcache = dir / "nc"
  createDir dir
  writeFile(dir / "p.nim", render(p))
  for x in walkDirRec(nimcache):  # a stale binary must not pass for a fresh one
    if x.extractFilename == "p": removeFile x
  var flags = ""
  for c in Cfgs:
    if c[0] == cfg: flags = c[1]
  let (o, rc) = execCmdEx(&"timeout 300 {nimony} {flags} --nimcache:{nimcache} {dir / \"p.nim\"}")
  var exe = ""
  for x in walkDirRec(nimcache):
    if x.extractFilename == "p" and fpUserExec in getFilePermissions(x): exe = x
  if rc != 0 or exe == "":
    actual = o
    return cfg & ":cfail:" & (if rc == 124: "timeout" else: errKey(o))
  let (ro, rrc) = execCmdEx("timeout 20 " & exe)
  actual = ro
  if rrc == 124: cfg & ":timeout"
  elif rrc != 0: cfg & ":crash:" & $rrc
  elif ro != exp: cfg & ":mismatch"
  else: ""

# ---- reducer --------------------------------------------------------------------

proc flatten(n: Node): seq[Node] =
  result = @[n]
  for x in n.exprs: result.add flatten(x)
  for x in n.body: result.add flatten(x)
  if n.fin != nil: result.add flatten(n.fin)

const
  IntKinds = {eVar, eCall, eAdd, eIfx, eTryx, eBlkx, eLen}
  ListKinds = {xProg, xProc, xBr, sFor, sBlock, sDefer}  ## `body` is a plain statement list

proc reduce(p: Node; sig: string): int =
  ## Shrinks `p` in place while `verdict` keeps returning `sig`; returns the tries.
  var tries = 0
  let cfg = beforeColon(sig)
  proc keep(): bool =
    inc tries
    tries <= budget and verdict(p, cfg) == sig
  var changed = true
  while changed and tries < budget:
    changed = false
    var k = 0
    while k < p.flatten.len and tries < budget:  # recomputed: an edit detaches nodes
      let n = p.flatten[k]
      inc k
      if n.kind in ListKinds + {sTry, sCase}:  # delete chunks: procs, statements, arms, of-branches
        let lo = ord(n.kind == sTry)   # keep the try body
        let hi = ord(n.kind == sCase)  # keep the else branch
        var c = max(1, (n.body.len - lo - hi) div 2)
        while c >= 1:
          var i = lo
          while i < n.body.len - hi:
            let old = n.body
            for _ in i ..< min(i + c, n.body.len - hi): n.body.delete(i)
            if keep(): changed = true
            else:
              n.body = old
              i += c
          c = c div 2
      if n.kind in ListKinds:  # unwrap compound statements, flatten multi-line lets
        var j = 0
        while j < n.body.len:
          let s = n.body[j]
          if s.kind in {sIf, sTry, sFor, sBlock, sDefer}:
            let inner = if s.kind in {sIf, sTry}: s.body[0].body else: s.body
            n.body.delete(j)
            for k, x in inner: n.body.insert(x, j + k)
            if keep():
              changed = true
              continue  # look at what was spliced in at j
            for _ in 0 ..< inner.len: n.body.delete(j)
            n.body.insert(s, j)
          elif s.kind == sLet and s.body.len > 0:
            let old = s.body
            s.body = @[]
            s.exprs = @[lit(1)]
            if keep(): changed = true
            else:
              s.body = old
              s.exprs = @[]
          inc j
      for i in 0 ..< n.exprs.len:  # an int expression -> 1 or one of its operands
        let x = n.exprs[i]
        if x.kind notin IntKinds: continue
        var ys = @[lit(1)]
        for y in x.exprs:
          if y.kind in IntKinds: ys.add y
        for y in ys:
          n.exprs[i] = y
          if keep():
            changed = true
            break
          n.exprs[i] = x
  tries

# ---- driver ---------------------------------------------------------------------

proc commented(s: string; dropEmpty = false): string =
  ## Every line of `s` as a `# ` comment line.
  for line in s.splitLines:
    if line != "" or not dropEmpty: result.add "# " & line & "\n"

proc trailer(p: Node): string =
  "# EXPECTED\n" & commented(expected(p), dropEmpty = true)

proc main() =
  var seed = int(epochTime()) mod 1_000_000
  var count = 10
  var outDir = getAppDir() / "out"
  var one = -1
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": work = val
    of "budget": budget = parseInt(val)
    of "allow": allow = val
    of "one": one = parseInt(val)
    else: quit "unknown option: " & key
  if one >= 0:
    let p = make(one)
    stdout.write render(p) & trailer(p)
    return
  nimony = absolutePath(nimony)
  work = absolutePath(work) / ("s" & $seed)  # one work dir per process
  createDir outDir
  let t0 = epochTime()
  var found = 0
  var seen: CountTable[string]
  for k in 0 ..< count:
    let s = seed + k
    let p = make(s)
    var sigs: seq[string]
    var outputs: seq[string]
    for c in Cfgs:
      let v = verdict(p, c[0])
      if v != "":
        sigs.add v
        outputs.add actual
        if c[0] == "c": break  # C already wrong: opt/n would only repeat it
    if sigs.len == 0: echo &"seed {s}: ok"
    for i, sig in sigs:
      inc found
      seen.inc sig
      echo &"seed {s}: {sig}"
      let base = outDir / &"{s}_{beforeColon(sig)}"
      writeFile(base & ".nim", render(p) & trailer(p) & "# ACTUAL\n" &
                commented(outputs[i]))
      let log = open(outDir / "log.csv", fmAppend)
      log.writeLine &"{epochTime() - t0:.1f},{k + 1},{s},{sig.replace(',', ';')}"
      log.close
      # reduce only the first few hits of a signature; one per compile error is enough
      if budget > 0 and seen[sig] <= (if ":cfail:" in sig: 1 else: 3):
        let m = make(s)  # a fresh copy: reduce works in place
        let n = reduce(m, sig)
        discard verdict(m, beforeColon(sig))  # refresh `actual` for the reduced program
        let src = render(m)
        writeFile(base & ".min.nim", &"# sig: {sig}\n# seed: {s}, {n} reduce tries\n" & src & trailer(m) &
                  "# ACTUAL\n" & commented(actual))
        echo &"  reduced to {src.countLines} lines ({n} tries): {base}.min.nim"
  echo &"{count} programs, {found} findings, {int(epochTime() - t0)}s — {outDir}"

main()
