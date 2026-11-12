## Optimizer differential fuzzer: `nimony c` against `nimony c --opt:speed`
## (or `nimony n` against `nimony n --opt:speed` with `--mode:n`).
##
## Derived from tools/difffuzz.nim (UB-free generator, bit-pattern printing,
## statement-deleting reducer), biased toward what an optimizer breaks:
## pointers and `addr` into locals/arrays/fields/globals, var params that alias
## a global the callee writes, early returns in inlinable procs, recursion,
## loops with `break`/`continue`, `case`, globals written by callees, checked
## signed `int` arithmetic and checked array indexing (overflow/bounds checks
## the optimizer may remove).
##
## A finding (opt build fails to compile, crashes, or prints differently) is
## triaged first: the opt build is rerun once per `SHOGGOTH_DISABLE=<pass>`,
## and the passes that make it go away join its signature. Only a new
## signature is reduced (statement-tree delta, then a line pass).
##
##   nim c -d:release -o:optfuzz optfuzz.nim
##   ./optfuzz --seed:1 --count:100 --out:out --work:work [--mode:n] [--time:SECONDS]
##   ./optfuzz --seed:1234 --emit             # print one program
##
## Every raw finding is appended to `<out>/log.csv`.

import std / [os, osproc, strutils, parseutils, random, times, strformat, parseopt, tables]

type
  Ty = enum tU64, tU32, tU8, tI32, tI64, tF64, tF32, tBool, tInt, tObj

  Node = ref object
    line: string                 ## the statement, or a block header ending in `:`
    kids: seq[Node]
    elseKids: seq[Node]
    hasElse: bool
    isCase: bool                 ## kids are `of` arms rendered at this indent

  HelperKind = enum
    hkPure, hkVar, hkVarObj, hkPtr, hkRec, hkGlobal  ## hkRec is pure too

  Helper = object
    name, decl: string
    params: seq[Ty]
    ret: Ty
    kind: HelperKind

  Gen = object
    r: Rand
    vars: seq[(string, Ty)]      ## readable scalars
    lvals: seq[(string, Ty)]     ## assignable scalars
    loopVars: seq[string]        ## `for` counters in scope (int)
    helpers: seq[Helper]
    depth, loopDepth: int
    haveObjs: bool               ## `v`, `w`, `arr`, `pa`, `pb`, `pv` are declared
    inHelper: bool               ## generating an effect helper's body
    hasRet: bool                 ## ... that returns a uint64
    uniq: int                    ## counter for unique `wc<n>` / `bl<n>` names

  Program = object
    helpers: seq[Helper]
    procs: seq[seq[Node]]        ## statement trees, one per `t<i>`
    procHeads: seq[seq[string]]  ## local declarations, one block per `t<i>`
    procPrinted: seq[seq[string]] ## what the final `echo` of each `t<i>` prints
    calls: seq[string]           ## `t<i>(…)` call per proc

  Outcome = enum  ## the strings name output files and log signatures
    oSame = "okSame", oMismatch = "mismatch", oCompile = "compileFails",
    oCrash = "runFails", oInvalid = "invalid"

  Result = object
    outcome: Outcome
    detail: string               ## why the base build failed
    baseOut, optOut: string      ## program output + exit code, or the opt compiler's error
    badProc: int                 ## the `t<i>` blamed, -1 if unknown

const
  ParamDecl = "p0: uint64; p1: float64; p2: uint32; p3: float32; p4: int32; p5: int"
  Params = [("p0", tU64), ("p1", tF64), ("p2", tU32), ("p3", tF32), ("p4", tI32), ("p5", tInt)]
  Passes = ["imi", "rewrite", "ctorproj", "scalarize", "copyprop", "unswitch", "indvars",
            "cse", "memidioms", "vectorize", "sinkret", "tailcall"]

proc tyName(t: Ty): string =
  case t
  of tU64: "uint64"
  of tU32: "uint32"
  of tU8: "uint8"
  of tI32: "int32"
  of tI64: "int64"
  of tF64: "float64"
  of tF32: "float32"
  of tBool: "bool"
  of tInt: "int"
  of tObj: "V"

proc suffix(t: Ty): string =
  case t
  of tU64: "'u64"
  of tU32: "'u32"
  of tU8: "'u8"
  of tI32: "'i32"
  of tI64: "'i64"
  of tF32: "'f32"
  else: ""

proc bitsOf(t: Ty; e: string): string =
  ## The printed form of a value: its bit pattern, with NaN canonicalized.
  case t
  of tU64, tU32, tU8, tInt: e
  of tI32: "cast[uint32](" & e & ")"
  of tI64: "cast[uint64](" & e & ")"
  of tF64: "(if " & e & " != " & e & ": 0x7ff8000000000000'u64 else: cast[uint64](" & e & "))"
  of tF32: "(if " & e & " != " & e & ": 0x7fc00000'u32 else: cast[uint32](" & e & "))"
  of tBool: "ord(" & e & ")"
  of tObj: e

proc pick[T](g: var Gen; xs: openArray[T]): T = xs[g.r.rand(xs.len - 1)]
proc chance(g: var Gen; p: float): bool = g.r.rand(1.0) < p

proc lit(g: var Gen; t: Ty): string =
  case t
  of tU64:
    let v = g.pick([0'u64, 1, 2, 3, 7, 255, 0x7fffffff, 0x80000000'u64,
                    0xffffffff'u64, 0x100000000'u64, 0x7fffffffffffffff'u64,
                    0x8000000000000000'u64, 0xffffffffffffffff'u64,
                    g.r.next(), g.r.next() shr 33])
    "0x" & toHex(v) & "'u64"
  of tU32:
    let v = g.pick([0'u32, 1, 2, 5, 255, 0x7fff, 0x8000, 0x7fffffff,
                    0x80000000'u32, 0xffffffff'u32, uint32(g.r.next() and 0xffffffff'u64)])
    "0x" & toHex(v) & "'u32"
  of tU8:
    $g.pick([0, 1, 2, 127, 128, 200, 255, g.r.rand(255)]) & "'u8"
  of tI32:
    "(" & $g.pick([0'i64, 1, -1, 2, -2, 0x7fffffff, -0x80000000'i64, 1000, -1000,
                   int64(g.r.rand(0x7fffffff)) - 0x40000000]) & "'i32)"
  of tI64:
    "(" & $g.pick([0'i64, 1, -1, high(int64), low(int64) + 1, 0x80000000'i64,
                   -0x80000000'i64, int64(g.r.next() shr 2) - (1'i64 shl 60)]) & "'i64)"
  of tInt:
    "(" & $g.pick([0, 1, -1, 2, 3, 7, -5, 100, 1000, -1000, 65535, g.r.rand(20000) - 10000]) & ")"
  of tF64:
    if g.chance(0.15):
      "cast[float64](0x" & toHex(g.pick([0x7ff0000000000000'u64, 0xfff0000000000000'u64,
        0x7ff8000000000000'u64, 0x0000000000000001'u64,
        0x8000000000000000'u64, 0x000fffffffffffff'u64, g.r.next()])) & "'u64)"
    else:
      g.pick(["0.0", "1.0", "-1.0", "0.5", "-1.5", "2.5", "3.141592653589793",
              "1e300", "-1e300", "1e-310", "1e10", "0.1", "-7.25", "65536.0",
              "9007199254740993.0", "-2147483648.0", "4294967296.0"])
  of tF32:
    if g.chance(0.15):
      "cast[float32](0x" & toHex(g.pick([0x7f800000'u32, 0xff800000'u32,
        0x7fc00000'u32, 0x00000001'u32, 0x80000000'u32,
        uint32(g.r.next() and 0xffffffff'u64)])) & "'u32)"
    else:
      g.pick(["0.0", "1.0", "-1.0", "0.5", "2.5", "3.4e38", "1e-40", "-0.25", "16777217.0"]) & "'f32"
  of tBool:
    g.pick(["true", "false"])
  of tObj:
    "V(x: 1.0, y: -2.0, n: 3'u32)"

proc expr(g: var Gen; t: Ty; d: int): string

proc index(g: var Gen): string =
  ## An array index: masked (always in range) or, rarely, a checked one that
  ## may be out of range (both builds must raise the same IndexDefect).
  if g.chance(0.03):
    "(" & g.expr(tInt, 1) & " mod 9)"
  else:
    "(" & g.expr(tU64, 1) & " and 7'u64)"

proc leaf(g: var Gen; t: Ty): string =
  ## A literal or a readable location of type `t`.
  var cands: seq[string] = @[]
  for (n, vt) in g.vars:
    if vt == t: cands.add n
  if g.haveObjs:
    case t
    of tF64: cands.add ["v.x", "v.y", "w.x", "pv.x", "gv.x"]
    of tU32: cands.add ["v.n", "w.n", "pv.n", "gv.n"]
    of tU64:
      cands.add ["arr[" & $g.r.rand(7) & "]", "pa[]", "pb[]", "pa[]",
                 "garr[" & $g.r.rand(7) & "]"]
    else: discard
  if t == tU64 or t == tInt:
    for lv in g.loopVars:
      cands.add(if t == tU64: "uint64(" & lv & ")" else: lv)
  if cands.len == 0 or g.chance(0.2): g.lit(t)
  else: g.pick(cands)

proc callPure(g: var Gen; t: Ty; d: int): string =
  ## A call of a pure helper returning `t`, or "" if there is none.
  var hs: seq[int] = @[]
  for i, h in g.helpers:
    if h.ret == t and h.kind in {hkPure, hkRec}: hs.add i
  if hs.len == 0: return ""
  let h = g.helpers[g.pick(hs)]
  if h.kind == hkRec:
    # mask the depth so the recursion stays shallow
    return h.name & "((" & g.expr(tU32, d - 1) & ") and 7'u32, " & g.expr(tU64, d - 1) & ")"
  var args: seq[string] = @[]
  for p in h.params:
    args.add(if p != tObj: g.expr(p, d - 1)
             elif g.haveObjs: g.pick(["v", "w", "pv[]"])
             else: "V(x: 1.0, y: -2.0, n: 3'u32)")
  h.name & "(" & args.join(", ") & ")"

proc expr(g: var Gen; t: Ty; d: int): string =
  if d <= 0 or g.chance(0.2): return g.leaf(t)
  template e(tt: Ty): string = g.expr(tt, d - 1)
  if g.chance(0.08):
    return "(if " & e(tBool) & ": " & e(t) & " else: " & e(t) & ")"
  if g.chance(0.10):
    let c = g.callPure(t, d)
    if c.len > 0: return c
  case t
  of tU64, tU32, tU8:
    let s = suffix(t)
    let mask = (case t
      of tU64: "63"
      of tU32: "31"
      else: "7") & s
    case g.r.rand(13)
    of 0..5:
      "(" & e(t) & " " & g.pick(["+", "-", "*", "xor", "and", "or"]) & " " & e(t) & ")"
    of 6: "(" & e(t) & " " & g.pick(["shl", "shr"]) & " (" & e(t) & " and " & mask & "))"
    of 7: "(" & e(t) & " " & g.pick(["div", "mod"]) & " (" & e(t) & " or 1" & s & "))"  # never 0
    of 8:
      case t
      of tU64: g.pick(["uint64(" & e(tU32) & ")", "uint64(" & e(tU8) & ")",
                       bitsOf(tF64, e(tF64)), "cast[uint64](" & e(tI64) & ")",
                       "cast[uint64](" & e(tInt) & ")"])
      of tU32: g.pick(["uint32(" & e(tU64) & " and 0xffffffff'u64)", "uint32(" & e(tU8) & ")",
                       "cast[uint32](" & e(tI32) & ")", bitsOf(tF32, e(tF32))])
      else: g.pick(["uint8(" & e(tU64) & " and 255'u64)", "uint8(" & e(tU32) & " and 255'u32)"])
    of 9: "(not " & e(t) & ")"
    of 10: tyName(t) & "(ord(" & e(tBool) & "))"
    else: g.leaf(t)
  of tInt:
    # checked signed arithmetic: an overflow raises, identically in both builds
    case g.r.rand(9)
    of 0..3: "(" & e(t) & " " & g.pick(["+", "-", "*", "+", "-"]) & " " & e(t) & ")"
    of 4: "(" & e(t) & " " & g.pick(["div", "mod"]) & " (" & e(tU8) & ".int or 1))"
    of 5: "int(" & e(tU8) & ")"
    of 6: "int(" & e(tU32) & " and 0xffff'u32)"
    of 7: "(" & e(t) & " " & g.pick(["and", "or", "xor"]) & " " & e(t) & ")"
    else: g.leaf(t)
  of tI32:
    case g.r.rand(3)
    of 0, 1: "cast[int32](" & e(tU32) & ")"
    else: g.leaf(t)
  of tI64:
    case g.r.rand(4)
    of 0, 1: "int64(" & e(tI32) & ")"
    of 2: "cast[int64](" & e(tU64) & ")"
    else: g.leaf(t)
  of tF64:
    case g.r.rand(15)
    of 0..4: "(" & e(t) & " " & g.pick(["+", "-", "*", "/"]) & " " & e(t) & ")"
    of 5: "(-(" & e(t) & "))"
    of 6: g.pick(["float64(" & e(tU32) & ")", "float64(" & e(tI32) & ")",
                  "float64(" & e(tI64) & ")", "float64(" & e(tU64) & ")",
                  "float64(" & e(tF32) & ")"])
    of 7: "cast[float64](" & e(tU64) & ")"
    of 8: g.pick(["sqrt", "floor", "trunc", "abs"]) & "(" & e(t) & ")"
    of 9: g.pick(["min", "max"]) & "(" & e(t) & ", " & e(t) & ")"
    else: g.leaf(t)
  of tF32:
    case g.r.rand(9)
    of 0..3: "(" & e(t) & " " & g.pick(["+", "-", "*", "/"]) & " " & e(t) & ")"
    of 4: g.pick(["float32(" & e(tF64) & ")", "float32(" & e(tU32) & ")",
                  "float32(" & e(tI32) & ")"])
    of 5: "cast[float32](" & e(tU32) & ")"
    else: g.leaf(t)
  of tObj:
    g.leaf(t)
  of tBool:
    case g.r.rand(7)
    of 0..3:
      let ct = g.pick([tU64, tU64, tU32, tU8, tI32, tInt, tInt, tF64, tF32])
      "(" & e(ct) & " " & g.pick(["<", "<=", "==", "!=", ">", ">="]) & " " & e(ct) & ")"
    of 4: "(" & e(tBool) & " " & g.pick(["and", "or"]) & " " & e(tBool) & ")"
    of 5: "(not " & e(tBool) & ")"
    of 6:
      let ft = g.pick([tF64, tF32])
      let x = e(ft)
      "(" & x & " != " & x & ")"
    else: g.leaf(t)

# ---- statements ---------------------------------------------------------------

proc stmts(g: var Gen; n: int): seq[Node]

proc u64Loc(g: var Gen): string =
  ## an addressable uint64 location for `addr`
  g.pick(["a0", "a1", "arr[" & $g.r.rand(7) & "]", "g0", "garr[" & $g.r.rand(7) & "]",
          "arr[" & g.index() & "]"])

proc effectCall(g: var Gen): string =
  ## A statement calling an effect helper. Its result goes to a plain local so
  ## no evaluation-order question arises.
  var hs: seq[int] = @[]
  for i, h in g.helpers:
    if h.kind in {hkVar, hkVarObj, hkPtr, hkGlobal}: hs.add i
  if hs.len == 0: return ""
  let h = g.helpers[g.pick(hs)]
  let dst = g.pick(["a0", "a1", "a0", "g0"])
  case h.kind
  of hkVar:
    # the var args may be globals the callee also writes directly: aliasing
    let x = g.pick(["a0", "a1", "g0", "arr[" & $g.r.rand(7) & "]", "pa[]", "garr[" & $g.r.rand(7) & "]"])
    let y = g.pick(["a2", "g1", "v.n", "w.n", "gv.n", "pv.n"])
    dst & " = " & h.name & "(" & x & ", " & y & ", " & g.expr(tU64, 2) & ")"
  of hkVarObj:
    h.name & "(" & g.pick(["v", "w", "gv", "pv[]"]) & ", " & g.expr(tU32, 2) & ")"
  of hkPtr:
    # `q` may equal `p`: the callee must not assume they don't alias
    let p = g.pick(["pa", "pb", "addr " & g.u64Loc()])
    let q = g.pick(["pa", "pb", p, "addr " & g.u64Loc()])
    dst & " = " & h.name & "(" & p & ", " & q & ", " & g.expr(tU64, 2) & ")"
  else:
    dst & " = " & h.name & "(" & g.expr(tU64, 2) & ")"

proc assignStmt(g: var Gen): Node =
  let (n, t) = g.pick(g.lvals)
  Node(line: n & " = " & g.expr(t, 3))

proc stmt(g: var Gen): Node =
  let d = 3
  let k = g.r.rand(119)  # one roll; the ranges below are the weights
  if k < 10 and g.depth < 2:
    inc g.depth
    result = Node(line: "if " & g.expr(tBool, 2) & ":", kids: g.stmts(1 + g.r.rand(3)))
    if g.chance(0.5):
      result.hasElse = true
      result.elseKids = g.stmts(1 + g.r.rand(2))
    dec g.depth
  elif k < 16 and g.depth < 2:
    inc g.depth
    inc g.loopDepth
    let lv = "k" & $g.loopVars.len
    g.loopVars.add lv
    result = Node(line: "for " & lv & " in 0 ..< " & $(1 + g.r.rand(4)) & ":",
                  kids: g.stmts(1 + g.r.rand(4)))
    discard g.loopVars.pop()
    dec g.loopDepth
    dec g.depth
  elif k < 19 and g.depth < 2:
    # while loop with its own counter
    inc g.depth
    inc g.loopDepth
    inc g.uniq
    let c = "wc" & $g.uniq
    let body = @[Node(line: "inc " & c)] & g.stmts(1 + g.r.rand(3))
    result = Node(line: "block:", kids: @[
      Node(line: "var " & c & " = 0"),
      Node(line: "while " & c & " < " & $(1 + g.r.rand(5)) & ":", kids: body)])
    dec g.loopDepth
    dec g.depth
  elif k < 21 and g.depth < 2:
    inc g.depth
    inc g.uniq
    let b = "bl" & $g.uniq
    var body = g.stmts(1 + g.r.rand(2))
    body.add Node(line: "if " & g.expr(tBool, 2) & ":", kids: @[Node(line: "break " & b)])
    body.add g.stmts(1 + g.r.rand(2))
    result = Node(line: "block " & b & ":", kids: body)
    dec g.depth
  elif k < 23 and g.depth < 2:
    inc g.depth
    result = Node(line: "case (" & g.expr(tU8, 2) & " and 3'u8)", isCase: true)
    for a in ["of 0'u8:", "of 1'u8, 2'u8:", "else:"]:
      result.kids.add Node(line: a, kids: g.stmts(1 + g.r.rand(2)))
    dec g.depth
  elif k < 26 and g.loopDepth > 0:
    result = Node(line: "if " & g.expr(tBool, 1) & ":", kids: @[Node(line: g.pick(["break", "continue"]))])
  elif k < 28 and g.inHelper:
    # early return
    let r = if g.hasRet: "return " & g.expr(tU64, 2) else: "return"
    result = Node(line: "if " & g.expr(tBool, 2) & ":", kids: @[Node(line: r)])
  elif g.inHelper or not g.haveObjs:
    # `v`, `pa`, ... are not in scope
    result = g.assignStmt()
  elif k < 34:
    result = Node(line: g.pick(["v", "w", "pv", "gv"]) & "." & g.pick(["x", "y"]) & " = " & g.expr(tF64, d))
  elif k < 38:
    result = Node(line: g.pick(["v", "w", "pv", "gv"]) & ".n = " & g.expr(tU32, d))
  elif k < 40:
    result = Node(line: g.pick(["v = w", "w = v", "gv = v", "v = gv", "pv[] = w", "w = pv[]"]))
  elif k < 44:
    result = Node(line: g.pick(["pa", "pb"]) & " = addr " & g.u64Loc())
  elif k < 46:
    result = Node(line: "pv = addr " & g.pick(["v", "w", "gv"]))
  elif k < 54:
    result = Node(line: g.pick(["pa[]", "pb[]", "pa[]"]) & " = " & g.expr(tU64, d))
  elif k < 60:
    result = Node(line: g.pick(["arr", "garr", "arr"]) & "[" & g.index() & "] = " & g.expr(tU64, d))
  elif k < 70:
    let c = g.effectCall()
    result = Node(line: (if c.len > 0: c else: "a0 = a1"))
  elif k < 74:
    result = (if g.chance(0.6): Node(line: "g0 = " & g.expr(tU64, d))
              else: Node(line: "g1 = " & g.expr(tU32, d)))
  elif k < 76:
    result = Node(line: g.pick(["inc", "dec"]) & " " & g.pick(["i0", "i1"]))
  else:
    result = g.assignStmt()

proc stmts(g: var Gen; n: int): seq[Node] =
  for i in 0 ..< n: result.add g.stmt()

# ---- helpers ---------------------------------------------------------------------

proc render(n: Node; indent: int; res: var string)

proc genPure(g: var Gen; i: int): Helper =
  ## A side-effect-free helper `h<i>`, callable inside expressions.
  let shapes = [(@[tF64, tF64], tF64), (@[tU64, tU32], tU64), (@[tObj, tF64], tObj),
                (@[tU64, tU64], tU64), (@[tInt, tU8], tInt), (@[tI32, tU32], tI32)]
  let (ps, ret) = g.pick(shapes)
  result = Helper(name: "h" & $i, params: ps, ret: ret, kind: hkPure)
  g.vars.setLen 0
  var decl: seq[string] = @[]
  var objParam = ""
  for j, p in ps:
    if p == tObj:
      decl.add "q" & $j & ": V"
      objParam = "q" & $j
    else:
      decl.add "q" & $j & ": " & tyName(p)
      g.vars.add ("q" & $j, p)
  if objParam.len > 0:
    g.vars.add (objParam & ".x", tF64)
    g.vars.add (objParam & ".n", tU32)
  let pragma = g.pick(["", "", " {.inline.}", " {.noinline.}"])
  var body: string
  if ret == tObj:
    body = "  V(x: " & g.expr(tF64, 2) & ", y: " & g.expr(tF64, 2) & ", n: " & g.expr(tU32, 2) & ")"
  elif g.chance(0.5):
    # multi-statement body with an early return
    body = "  var l0 = " & g.expr(ret, 2) & "\n" &
           "  if " & g.expr(tBool, 2) & ":\n    return " & g.expr(ret, 2) & "\n" &
           "  l0 = " & g.expr(ret, 2) & "\n" &
           "  result = l0"
  else:
    body = "  " & g.expr(ret, 3)
  result.decl = "proc " & result.name & "(" & decl.join("; ") & "): " &
                tyName(ret) & pragma & " =\n" & body

proc genEffect(g: var Gen; i: int; kind: HelperKind): Helper =
  ## An effect helper `e<i>`: a statement body that writes its params or globals.
  result = Helper(name: "e" & $i, kind: kind, ret: tU64)
  g.hasRet = kind != hkVarObj
  g.vars.setLen 0
  g.lvals.setLen 0
  g.inHelper = true
  g.haveObjs = false
  g.depth = 0
  g.loopDepth = 0
  var head: string
  let pragma = g.pick(["", "", " {.inline.}", " {.noinline.}"])
  # globals are visible to every effect helper
  for gl in [("g0", tU64), ("g1", tU32), ("garr[" & $g.r.rand(7) & "]", tU64), ("gv.x", tF64)]:
    g.vars.add gl
    g.lvals.add gl
  case kind
  of hkVar:
    head = "proc " & result.name & "(x: var uint64; y: var uint32; z: uint64): uint64" & pragma & " ="
    g.vars.add [("x", tU64), ("y", tU32), ("z", tU64)]
    g.lvals.add [("x", tU64), ("y", tU32), ("x", tU64)]
  of hkVarObj:
    head = "proc " & result.name & "(o: var V; k: uint32)" & pragma & " ="
    g.vars.add [("o.x", tF64), ("o.n", tU32), ("k", tU32)]
    g.lvals.add [("o.x", tF64), ("o.y", tF64), ("o.n", tU32), ("o.n", tU32)]
  of hkPtr:
    head = "proc " & result.name & "(p, q: ptr uint64; z: uint64): uint64" & pragma & " ="
    g.vars.add [("p[]", tU64), ("q[]", tU64), ("z", tU64)]
    g.lvals.add [("p[]", tU64), ("q[]", tU64), ("p[]", tU64), ("q[]", tU64)]
  of hkRec:
    head = "proc " & result.name & "(n: uint32; acc: uint64): uint64" & pragma & " ="
    g.vars.setLen 0
    g.vars.add [("n", tU32), ("acc", tU64)]
    result.decl = head & "\n  if n == 0'u32: return acc\n" &
      "  var l = " & g.expr(tU64, 2) & "\n" &
      "  if " & g.expr(tBool, 2) & ":\n    l = l xor " & g.expr(tU64, 1) & "\n" &
      "  result = " & result.name & "(n - 1'u32, l)" &
      (if g.chance(0.5): " + " & g.expr(tU64, 1) else: "")
    g.inHelper = false
    return
  else:
    head = "proc " & result.name & "(z: uint64): uint64" & pragma & " ="
    g.vars.add ("z", tU64)
  let l0init = g.expr(tU64, 1)
  g.vars.add ("l0", tU64)
  g.lvals.add ("l0", tU64)
  let body = g.stmts(2 + g.r.rand(5))
  # assumeSync: the body writes globals, which nimony otherwise rejects
  var s = head & "\n  {.cast(assumeSync).}:\n    var l0 = " & l0init & "\n"
  for n in body: render(n, 4, s)
  if g.hasRet: s.add "    result = " & g.expr(tU64, 2) & "\n"
  result.decl = s.strip(leading = false)
  g.inHelper = false

proc genProc(g: var Gen; i: int): (seq[string], seq[Node], seq[string], string) =
  ## Proc `t<i>`: (local declarations, body, printed values, call in `main`).
  g.haveObjs = false
  g.inHelper = false
  g.depth = 0
  g.loopDepth = 0
  g.vars.setLen 0
  g.lvals.setLen 0
  for p in Params: g.vars.add p
  var head: seq[string] = @[]
  let locals = [tU64, tU64, tU32, tU8, tI32, tI64, tF64, tF64, tF32, tBool, tInt, tInt]
  var printed: seq[string] = @[]
  for j, t in locals:
    let name = if t == tInt: "i" & $(j - 10) else: "a" & $j
    let init = g.expr(t, 2)
    head.add "  var " & name & ": " & tyName(t) & " = " & init
    g.vars.add (name, t)
    g.lvals.add (name, t)
    printed.add bitsOf(t, name)
  g.vars.add [("g0", tU64), ("g1", tU32)]
  head.add "  var v = V(x: " & g.expr(tF64, 1) & ", y: " & g.expr(tF64, 1) & ", n: " & g.expr(tU32, 1) & ")"
  head.add "  var w = V(x: " & g.expr(tF64, 1) & ", y: p1, n: p2)"
  var elems: seq[string] = @[]
  for k in 0 ..< 8: elems.add "p0 + " & $k & "'u64"
  head.add "  var arr: array[8, uint64] = [" & elems.join(", ") & "]"
  head.add "  var pa: ptr uint64 = addr " & g.pick(["a0", "a1", "arr[3]", "g0"])
  head.add "  var pb: ptr uint64 = addr " & g.pick(["a0", "arr[3]", "arr[0]", "garr[2]"])
  head.add "  var pv: ptr V = addr " & g.pick(["v", "w", "gv"])
  g.haveObjs = true
  let body = g.stmts(8 + g.r.rand(16))
  for f in ["v.x", "v.y", "w.x", "w.y", "gv.x", "gv.y"]: printed.add bitsOf(tF64, f)
  printed.add ["v.n", "w.n", "gv.n", "pa[]", "pb[]", "g0", "g1"]
  for j in 0 ..< 8: printed.add "arr[" & $j & "]"
  for j in 0 ..< 8: printed.add "garr[" & $j & "]"
  let call = "t" & $i & "(" & g.lit(tU64) & ", " & g.lit(tF64) & ", " & g.lit(tU32) &
             ", " & g.lit(tF32) & ", " & g.lit(tI32) & ", " & g.lit(tInt) & ")"
  (head, body, printed, call)

proc generate(seed, nprocs: int): Program =
  var g = Gen(r: initRand(seed))
  for i in 0 ..< 3: g.helpers.add g.genPure(i)
  for i, kind in [hkVar, hkVarObj, hkPtr, hkRec, hkGlobal, HelperKind(g.r.rand(1..5))]:
    g.helpers.add g.genEffect(i, kind)
  result.helpers = g.helpers
  for i in 0 ..< nprocs:
    # own seed per proc: `t<i>` does not depend on the helpers or other procs
    g.r = initRand(seed * 1000 + i + 1)
    let (head, body, printed, call) = g.genProc(i)
    result.procHeads.add head
    result.procs.add body
    result.procPrinted.add printed
    result.calls.add call

# ---- rendering ------------------------------------------------------------------

proc render(n: Node; indent: int; res: var string) =
  let pad = repeat(' ', indent)
  res.add pad & n.line & "\n"
  if n.isCase:
    for k in n.kids: render(k, indent, res)
  elif n.line.endsWith(":"):
    if n.kids.len == 0: res.add pad & "  discard\n"
    for k in n.kids: render(k, indent + 2, res)
    if n.hasElse:
      res.add pad & "else:\n"
      if n.elseKids.len == 0: res.add pad & "  discard\n"
      for k in n.elseKids: render(k, indent + 2, res)

proc render(p: Program; only: int = -1): string =
  ## The program source; with `only >= 0` just the proc `t<only>`.
  result = "# generated by optfuzz\nimport std/[syncio, math]\n\n" &
           "type V = object\n  x, y: float64\n  n: uint32\n\n" &
           "var g0: uint64 = 0x1234'u64\nvar g1: uint32 = 7'u32\n" &
           "var garr: array[8, uint64] = [1'u64, 2'u64, 3'u64, 4'u64, 5'u64, 6'u64, 7'u64, 8'u64]\n" &
           "var gv = V(x: 0.5, y: 1.5, n: 9'u32)\n\n"
  for h in p.helpers: result.add h.decl & "\n\n"
  for i in 0 ..< p.procs.len:
    if only >= 0 and i != only: continue
    result.add "proc t" & $i & "(" & ParamDecl & ") =\n  {.cast(assumeSync).}:\n"
    for l in p.procHeads[i]: result.add "  " & l & "\n"
    for n in p.procs[i]: render(n, 4, result)
    result.add "    echo \"t" & $i & " \", " & p.procPrinted[i].join(", \" \", ") & "\n\n"
  result.add "proc main() =\n"
  for i in 0 ..< p.calls.len:
    if only >= 0 and i != only: continue
    result.add "  " & p.calls[i] & "\n"
  result.add "\nmain()\n"

# ---- running ----------------------------------------------------------------------

var nimonyExe = "/home/ageralis/Projects/nimony/bin/nimony"
var backend = "c"
var workDir = "work"

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

proc buildRun(file, tag, extra: string; disable = ""): (bool, string) =
  ## (compiled, output + exit code, or the compiler's error)
  let dir = workDir / tag
  removeDir(dir)
  createDir(dir)
  if disable != "": putEnv("SHOGGOTH_DISABLE", disable)   # the pass to switch off
  let (outp, code) = run(quoteShell(nimonyExe) & " " & backend & " " & extra &
                         " --nimcache:" & quoteShell(dir) & " " & quoteShell(file), 300)
  if disable != "": delEnv("SHOGGOTH_DISABLE")
  if code != 0: return (false, outp)
  var exe = ""
  for f in walkDirRec(dir):
    if f.extractFilename == "fz" & Exe: exe = f
  if exe.len == 0: return (false, "no executable produced\n" & outp)
  let (r, rc) = run(quoteShell(exe), 10)
  (true, r & "\nexit code " & $rc)

proc firstDiffProc(a, b: string): int =
  ## The `t<i>` whose output line first differs between `a` and `b`.
  let la = a.splitLines
  let lb = b.splitLines
  for i in 0 ..< max(la.len, lb.len):
    let x = if i < la.len: la[i] else: ""
    let y = if i < lb.len: lb[i] else: ""
    if x != y:
      for s in [x, y]:
        if s.startsWith("t"):
          let sp = s.find(' ')
          if sp > 1:
            try: return parseInt(s[1 ..< sp]) except ValueError: discard
      # a crash: the proc after the last printed line
      var last = -1
      for j in 0 ..< i:
        if la[j].startsWith("t"):
          let sp = la[j].find(' ')
          try: last = parseInt(la[j].substr(1, sp - 1)) except ValueError: discard
      return last + 1
  -1

proc check(src: string; disable = ""; knownBase = ""): Result =
  ## Base build vs `--opt:speed` build (with `env`); `knownBase` skips the base build.
  createDir(workDir)
  let file = workDir / "fz.nim"
  writeFile(file, src)
  let (baseOk, baseOut) = if knownBase.len > 0: (true, knownBase) else: buildRun(file, "base", "")
  if not baseOk:
    return Result(outcome: oInvalid, detail: "base build: " & baseOut)
  let (optOk, optOut) = buildRun(file, "opt", "--opt:speed", disable)
  if not optOk:
    # blame the proc nimony names in its error, if any
    var bad = -1
    let k = optOut.find("in proc t")
    if k >= 0:
      var j = k + "in proc t".len
      var num = ""
      while j < optOut.len and optOut[j] in {'0'..'9'}:
        num.add optOut[j]; inc j
      if num.len > 0: bad = parseInt(num)
    return Result(outcome: oCompile, baseOut: baseOut, optOut: optOut, badProc: bad)
  if baseOut != optOut:
    let crashed = not optOut.endsWith("exit code 0") and baseOut.endsWith("exit code 0")
    return Result(outcome: (if crashed: oCrash else: oMismatch), baseOut: baseOut, optOut: optOut,
                  badProc: firstDiffProc(baseOut, optOut))
  Result(outcome: oSame)

proc normKey(s: string): string =
  ## The error line of a compile failure with numbers blurred, for dedupe.
  var key = ""
  for l in s.splitLines:
    if "Error" in l or "Assertion" in l or "error:" in l or "BUG" in l:
      key = l.strip
      break
  if key.len == 0:
    for l in s.splitLines:
      if not l.isEmptyOrWhitespace:
        key = l.strip
        break
  var i = 0
  while i < key.len:
    if key[i] in {'0'..'9'}:
      result.add '#'
      while i < key.len and key[i] in {'0'..'9'}: inc i
    else:
      result.add key[i]; inc i

proc sameFailure(a, b: Result): bool =
  if a.outcome != b.outcome: return false
  if a.outcome == oCompile: return normKey(a.optOut) == normKey(b.optOut)
  true

var reduceBudget = 120  ## max test builds per reduction

proc reduce(p: var Program; target: Result; only: int): string =
  ## Shrinks `p` (just `t<only>` if `only >= 0`) while it fails like `target`.
  var tests = 0
  proc still(p: Program): bool =
    inc tests
    if tests > reduceBudget: return false
    sameFailure(check(render(p, only)), target)

  proc tryList(p: var Program; list: var seq[Node]): bool =
    # `list` lives inside `p`, so editing it in place changes what `still` renders
    result = false
    var i = 0
    while i < list.len:
      let saved = list[i]
      list.delete(i)
      if still(p):
        result = true
        continue
      list.insert(saved, i)
      # replace a compound statement by its body
      if saved.kids.len > 0 and not saved.isCase:
        list.delete(i)
        for j, k in saved.kids: list.insert(k, i + j)
        if still(p):
          result = true
          continue
        for j in 0 ..< saved.kids.len: list.delete(i)
        list.insert(saved, i)
      if saved.kids.len > 0:
        if saved.isCase:
          for arm in saved.kids:
            if tryList(p, arm.kids): result = true
        elif tryList(p, saved.kids): result = true
        if saved.hasElse and tryList(p, saved.elseKids): result = true
      inc i

  # print only the values that differ, so less code stays live
  if only >= 0 and target.outcome == oMismatch:
    let la = target.baseOut.splitLines
    let lb = target.optOut.splitLines
    for k in 0 ..< min(la.len, lb.len):
      if la[k] != lb[k] and la[k].startsWith("t" & $only & " "):
        let xa = la[k].split(' ')
        let xb = lb[k].split(' ')
        var differing: seq[string] = @[]
        for c in 1 ..< min(xa.len, xb.len):
          if xa[c] != xb[c] and c - 1 < p.procPrinted[only].len:
            differing.add p.procPrinted[only][c - 1]
        if differing.len > 0:
          let saved = p.procPrinted[only]
          p.procPrinted[only] = differing
          inc tests
          # the output itself changes, so `still` cannot judge this: any difference counts
          if check(render(p, only)).outcome != oMismatch: p.procPrinted[only] = saved
        break

  var changed = true
  while changed and tests <= reduceBudget:
    changed = false
    for pi in 0 ..< p.procs.len:
      if only >= 0 and pi != only: continue
      if tryList(p, p.procs[pi]): changed = true
  # line-level pass: unused helpers, declarations, helper statements
  var lines = render(p, only).splitLines
  var i = 0
  while i < lines.len and tests <= reduceBudget:
    let l = lines[i]
    let ind = l.skipWhitespace
    # the skeleton: deleting these only breaks the program
    let keep = l.len == 0 or l.startsWith("import") or l.startsWith("type") or
               l.startsWith("  x, y") or l.startsWith("  n: uint32") or
               l.startsWith("proc t") or l.startsWith("proc main") or
               l.startsWith("main()") or l.continuesWith("echo", ind) or
               l.continuesWith("{.cast", ind) or (l.startsWith("  t") and "(" in l)
    if not keep:
      var cand = lines
      cand.delete(i)
      inc tests
      if sameFailure(check(cand.join("\n")), target):
        lines = cand
        continue
    inc i
  lines.join("\n")

proc bisectPasses(src: string; target: Result): string =
  ## The passes whose `SHOGGOTH_DISABLE=<pass>` alone makes the failure go away.
  var fixes: seq[string] = @[]
  for pass in Passes:
    # the base output is known, so only the opt build reruns
    let r = check(src, pass, target.baseOut)
    if not sameFailure(r, target) and r.outcome != oInvalid: fixes.add pass
  if fixes.len == 0: "none (no single pass disable fixes it)" else: fixes.join(",")

# ---- driver ------------------------------------------------------------------------

proc main() =
  var seed = 1
  var count = 1_000_000
  var nprocs = 6
  var outDir = "out"
  var doReduce = true
  var minutes = 0.0
  var emit = false
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "procs": nprocs = parseInt(val)
    of "mode": backend = val
    of "nimony": nimonyExe = val
    of "out": outDir = val
    of "work": workDir = val
    of "budget": reduceBudget = parseInt(val)
    of "noreduce": doReduce = false
    of "minutes": minutes = parseFloat(val)
    of "emit": emit = true
    else: quit "unknown option: " & key
  if emit:
    echo render(generate(seed, nprocs)); return
  workDir = absolutePath(workDir)
  createDir(outDir)
  let start = epochTime()
  var programs, found, invalidCount = 0
  var seen = initTable[string, string]()   # signature -> first finding
  for k in 0 ..< count:
    if minutes > 0 and epochTime() - start > minutes * 60: break
    let s = seed + k
    var p = generate(s, nprocs)
    let res = check(render(p))
    inc programs
    let el = int(epochTime() - start)
    case res.outcome
    of oSame:
      echo &"[{el}s] seed {s}: same"
    of oInvalid:
      inc invalidCount
      echo &"[{el}s] seed {s}: INVALID"
      writeFile(outDir / &"invalid_{s}.nim", render(p))
      writeFile(outDir / &"invalid_{s}.txt", res.detail)
    else:
      inc found
      let stem = outDir / &"{backend}_{res.outcome}_{s}"
      var sig = $res.outcome
      if res.outcome == oCompile: sig.add ": " & normKey(res.optOut)
      else: sig.add " [" & bisectPasses(render(p), res) & "]"   # triage before reducing
      echo &"[{el}s] seed {s}: {sig} (proc t{res.badProc})"
      let f = open(outDir / "log.csv", fmAppend)
      f.write &"{el},{programs},{backend}_{s},\"{sig.replace(\"\\\"\", \"'\")}\"\n"
      f.close()
      writeFile(stem & ".nim", render(p))
      writeFile(stem & ".base.txt", res.baseOut)
      writeFile(stem & ".opt.txt", res.optOut)
      if sig in seen:
        echo "  duplicate of ", seen[sig]
      elif doReduce:
        # reduce just the blamed proc if it fails the same way on its own
        var only = res.badProc
        if only >= 0 and not sameFailure(check(render(p, only)), res): only = -1
        let reduced = reduce(p, res, only)
        let after = check(reduced)
        writeFile(stem & ".reduced.nim", reduced)
        writeFile(stem & ".reduced.base.txt", after.baseOut)
        writeFile(stem & ".reduced.opt.txt", after.optOut)
        let passes = bisectPasses(reduced, after)
        writeFile(stem & ".passes.txt", passes & "\n")
        echo &"  reduced to {reduced.countLines} lines ({after.outcome}); passes: {passes}"
        seen[sig] = stem
  echo &"{programs} programs, {found} findings, {invalidCount} invalid — {outDir}"

main()
