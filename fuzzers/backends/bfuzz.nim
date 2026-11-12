## Differential fuzzer: `nimony c` against `nimony n`, `l`, `j` and `w`.
##
## Extended copy of tools/difffuzz.nim. Generates random, UB-free Nimony
## programs from a seed, builds each with every backend (C/gcc is the oracle;
## JS and wasm run under node) and compares the output. Every value prints as
## its BIT PATTERN. A backend whose compile, exit or output differs from C is
## blamed; when all other backends agree and only C differs, C is blamed.
##
## On top of difffuzz's generator: signed wrapping `+ - *`, `div/mod` by a
## positive, shifts and negation on int8/16/32/64 (Nimony defines signed
## overflow as wrapping), narrowing/widening conversions, uint16,
## `{.keepOverflowFlag.}` checked helpers, helpers with 6..17 mixed parameters
## whose result folds every parameter (ABI), small (`S`) and large (`B`)
## objects by value, `array[3, array[4, int32]]`, `case`, `while` with
## `break`/`continue`, string building. Narrow checked helpers and narrow
## `case` labels appear in only 12% of programs (known rejections).
##
## The reducer is difffuzz's: keep the failing `t<i>`, delete statements while
## the failure persists, then a line pass.
##
##   nim c -d:release -o:bin/bfuzz bfuzz.nim
##   bin/bfuzz --seed:1000000 --count:100 --out:out --work:work
##   bin/bfuzz --seed:1234 --emit             # print one program
##   bin/bfuzz --backends:c,n --time:600 --noreduce
##
## Every raw finding is appended to `<out>/events.csv`.

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables]

type
  Ty = enum tU64, tU32, tU8, tI32, tI64, tF64, tF32, tBool, tObj,  ## tObj: `V`
    tI8, tI16, tU16, tS, tB  ## tS: small object `S` (8 bytes), tB: large `B` (48)

  Node = ref object
    prelude: string              ## line before the statement (`wc1 = 0`)
    bodyPre: seq[string]         ## first body lines, never reduced (`inc wc1`)
    arms: seq[Node]              ## `of`/`else` arms of a `case`
    line: string                 ## the statement, or an `if`/`for` header
    kids: seq[Node]              ## body of `if`/`for`
    elseKids: seq[Node]          ## `else` body of an `if`
    hasElse: bool

  Helper = object                ## a generated top-level proc `h<i>`
    name, decl: string
    params: seq[Ty]
    ret: Ty

  Gen = object                   ## generator state for one program
    rng: Rand
    vars: seq[(string, Ty)]      ## scalar locals and parameters in scope
    loopVars: seq[string]        ## `for` counters in scope (int)
    helpers: seq[Helper]
    nest: int                    ## `if`/`for`/`case`/`while` nesting, capped at 2
    haveObjs: bool               ## `v`, `w`, `arr` are declared (not in helpers,
                                 ## not in the locals' initializers)
    loopDepth: int               ## inside `for`/`while`: break/continue allowed
    narrowOvf: bool              ## checked helpers on int8/16/32 too (native: report 90)
    narrowCase: bool             ## `case` with typed narrow labels (l, j, w reject it)

  Program = object               ## kept structured so the reducer can edit it
    helpers: seq[Helper]
    bodies: seq[seq[Node]]       ## statement trees, one per `t<i>`
    heads: seq[seq[string]]      ## local declarations, one block per `t<i>`
    printed: seq[seq[string]]    ## what the final `echo` of each `t<i>` prints
    calls: seq[string]           ## `t<i>(…)` call per proc
    narrowOvf: bool

  Outcome = enum   # unprefixed: `$outcome` goes into file names and events.csv
    okSame, mismatch, compileFails, runFails, invalid

  Verdict = object               ## one backend's result against C
    outcome: Outcome
    detail, outC, outOther: string  ## compile error; output of C and of the other backend
    badProc: int                 ## the `t<i>` that differs, or -1

const
  ParamDecl = "p0: uint64; p1: float64; p2: uint32; p3: float32; p4: int32"
  Params = [("p0", tU64), ("p1", tF64), ("p2", tU32), ("p3", tF32), ("p4", tI32)]
  Narrow = [("i8v", tI8), ("i16v", tI16), ("i32v", tI32), ("i64v", tI64), ("u16v", tU16)]

proc tyName(t: Ty): string =
  ## The Nim type name of `t`.
  case t
  of tU64: "uint64"
  of tU32: "uint32"
  of tU8: "uint8"
  of tI32: "int32"
  of tI64: "int64"
  of tF64: "float64"
  of tF32: "float32"
  of tBool: "bool"
  of tObj: "V"
  of tI8: "int8"
  of tI16: "int16"
  of tU16: "uint16"
  of tS: "S"
  of tB: "B"

proc suffix(t: Ty): string =
  ## The literal suffix of `t` (`'u64`), "" when it has none.
  case t
  of tU64: "'u64"
  of tU32: "'u32"
  of tU8: "'u8"
  of tI32: "'i32"
  of tI64: "'i64"
  of tF32: "'f32"
  of tI8: "'i8"
  of tI16: "'i16"
  of tU16: "'u16"
  else: ""

proc bitWidth(t: Ty): int =
  case t
  of tU8, tI8: 8
  of tU16, tI16: 16
  of tU32, tI32, tF32: 32
  else: 64

proc bitsOf(t: Ty; e: string): string =
  ## The printed form of a value: its bit pattern, never a formatted float.
  case t
  of tU64, tU32, tU8, tU16, tObj, tS, tB: e
  of tI8: "cast[uint8](" & e & ")"
  of tI16: "cast[uint16](" & e & ")"
  of tI32: "cast[uint32](" & e & ")"
  of tI64: "cast[uint64](" & e & ")"
  # A NaN prints canonically: IEEE 754 leaves its sign and payload to the
  # implementation (x86 `sqrtsd` makes a negative default NaN where gcc's
  # constant folder makes a positive one), so they are not a finding.
  of tF64: "(if " & e & " != " & e & ": 0x7ff8000000000000'u64 else: cast[uint64](" & e & "))"
  of tF32: "(if " & e & " != " & e & ": 0x7fc00000'u32 else: cast[uint32](" & e & "))"
  of tBool: "ord(" & e & ")"

# ---- literals ---------------------------------------------------------------

proc pick[T](g: var Gen; xs: openArray[T]): T = xs[g.rng.rand(xs.len - 1)]
proc chance(g: var Gen; p: float): bool = g.rng.rand(1.0) < p

proc lit(g: var Gen; t: Ty): string =
  case t
  of tU64:
    let v = g.pick([0'u64, 1, 2, 3, 7, 255, 0x7fffffff, 0x80000000'u64,
                    0xffffffff'u64, 0x100000000'u64, 0x7fffffffffffffff'u64,
                    0x8000000000000000'u64, 0xffffffffffffffff'u64,
                    g.rng.next(), g.rng.next() shr 33])
    "0x" & toHex(v) & "'u64"
  of tU32:
    let v = g.pick([0'u32, 1, 2, 5, 255, 0x7fff, 0x8000, 0x7fffffff,
                    0x80000000'u32, 0xffffffff'u32, uint32(g.rng.next() and 0xffffffff'u64)])
    "0x" & toHex(v) & "'u32"
  of tU8:
    $g.pick([0, 1, 2, 127, 128, 200, 255, g.rng.rand(255)]) & "'u8"
  of tI32:
    "(" & $g.pick([0'i64, 1, -1, 2, -2, 0x7fffffff, -0x80000000'i64, 1000, -1000,
                   int64(g.rng.rand(0x7fffffff)) - 0x40000000]) & "'i32)"
  of tI64:
    "(" & $g.pick([0'i64, 1, -1, high(int64), low(int64) + 1, 0x80000000'i64,
                   -0x80000000'i64, int64(g.rng.next() shr 2) - (1'i64 shl 60)]) & "'i64)"
  of tF64:
    if g.chance(0.15):
      "cast[float64](0x" & toHex(g.pick([0x7ff0000000000000'u64, 0xfff0000000000000'u64,
        0x7ff8000000000000'u64, 0x7ff0000000000001'u64, 0x0000000000000001'u64,
        0x8000000000000000'u64, 0x000fffffffffffff'u64, g.rng.next()])) & "'u64)"
    else:
      g.pick(["0.0", "1.0", "-1.0", "0.5", "-1.5", "2.5", "3.141592653589793",
              "1e300", "-1e300", "1e-310", "1e10", "0.1", "-7.25", "65536.0",
              "9007199254740993.0", "-2147483648.0", "4294967296.0"])
  of tF32:
    if g.chance(0.15):
      "cast[float32](0x" & toHex(g.pick([0x7f800000'u32, 0xff800000'u32,
        0x7fc00000'u32, 0x00000001'u32, 0x80000000'u32,
        uint32(g.rng.next() and 0xffffffff'u64)])) & "'u32)"
    else:
      g.pick(["0.0", "1.0", "-1.0", "0.5", "2.5", "3.4e38", "1e-40", "-0.25", "16777217.0"]) & "'f32"
  of tBool:
    g.pick(["true", "false"])
  of tObj:
    "V(x: 1.0, y: -2.0, n: 3'u32)"
  of tI8:
    "(" & $g.pick([0, 1, -1, 127, -128, 100, -100, g.rng.rand(255) - 128]) & "'i8)"
  of tI16:
    "(" & $g.pick([0, 1, -1, 32767, -32768, 300, -300, g.rng.rand(65535) - 32768]) & "'i16)"
  of tU16:
    $g.pick([0, 1, 255, 256, 32767, 32768, 65535, g.rng.rand(65535)]) & "'u16"
  of tS:
    "S(a: -3'i16, b: 5'i8, c: 1.5'f32)"
  of tB:
    "B(q: [1'u64, 2'u64, 3'u64, 4'u64], d: -0.5, e: -7'i8)"

# ---- expressions ------------------------------------------------------------

proc expr(g: var Gen; t: Ty; depth: int): string

proc leaf(g: var Gen; t: Ty): string =
  ## A variable, field, element or literal of type `t`.
  var cands: seq[string] = @[]
  for (n, vt) in g.vars:
    if vt == t: cands.add n
  if g.haveObjs:
    case t
    of tF64: cands.add ["v.x", "v.y", "w.x"]
    of tU32: cands.add ["v.n", "w.n"]
    of tU64:
      cands.add "arr[" & "(" & g.pick(["p0", "a0", "0x5'u64"]) & ") and 7'u64]"
      cands.add ["b0.q[" & $g.rng.rand(3) & "]", "b1.q[(a0 and 3'u64)]"]
    of tI32: cands.add ["mat[" & $g.rng.rand(2) & "][" & $g.rng.rand(3) & "]", "sumMat(mat)",
                        "mat[(a0 mod 3'u64)][(p0 and 3'u64)]"]
    of tI16: cands.add ["s0.a", "s1.a"]
    of tI8: cands.add ["s0.b", "b0.e"]
    of tF32: cands.add ["s0.c", "s1.c"]
    of tS: cands.add ["s0", "s1"]
    of tB: cands.add ["b0", "b1"]
    of tBool: cands.add ["(sb.len mod 3 == 1)", "(sb.len > 5)"]
    else: discard
  if t == tU64:
    for lv in g.loopVars: cands.add "uint64(" & lv & ")"
  if t == tI32:
    for lv in g.loopVars: cands.add "int32(" & lv & ")"
  if cands.len == 0 or g.chance(0.25): g.lit(t)
  else: g.pick(cands)

proc callHelper(g: var Gen; t: Ty; depth: int): string =
  ## A call to a generated helper returning `t`, or "" when there is none.
  var hs: seq[int] = @[]
  for i, h in g.helpers:
    if h.ret == t: hs.add i
  if hs.len == 0: return ""
  let h = g.helpers[g.pick(hs)]
  var args: seq[string] = @[]
  for p in h.params:
    args.add(if p notin {tObj, tS, tB}: g.expr(p, depth - 1)
             elif p == tObj and g.haveObjs: g.pick(["v", "w"])
             elif p == tS and g.haveObjs: g.pick(["s0", "s1"])
             elif p == tB and g.haveObjs: g.pick(["b0", "b1"])
             else: g.lit(p))
  h.name & "(" & args.join(", ") & ")"

proc cond(g: var Gen; depth: int): string =
  g.expr(tBool, depth)

proc expr(g: var Gen; t: Ty; depth: int): string =
  ## A random UB-free expression of type `t`, nested at most `depth` deep.
  if depth <= 0 or g.chance(0.2): return g.leaf(t)
  template e(tt: Ty): string = g.expr(tt, depth - 1)
  if g.chance(0.08):
    return "(if " & g.cond(depth - 1) & ": " & e(t) & " else: " & e(t) & ")"
  if g.chance(0.06):
    let c = g.callHelper(t, depth)
    if c.len > 0: return c
  case t
  of tI8, tI16, tI32, tI64:
    let s = suffix(t)
    let mask = $(bitWidth(t) - 1) & s
    let k = g.rng.rand(19)
    case k
    of 0..4: "(" & e(t) & " " & g.pick(["+", "-", "*"]) & " " & e(t) & ")"
    of 5: "(" & e(t) & " " & g.pick(["xor", "and", "or"]) & " " & e(t) & ")"
    # divisor in 1..64 (no zero, no `low div -1`); shift count masked below the width
    of 6: "(" & e(t) & " " & g.pick(["div", "mod"]) & " ((" & e(t) & " and 63" & s & ") + 1" & s & "))"
    of 7: "(" & e(t) & " " & g.pick(["shl", "shr"]) & " (" & e(t) & " and " & mask & "))"
    of 8: "(-(" & e(t) & "))"       # signed overflow wraps in Nimony: `-low` is defined
    of 9, 10:   # narrowing / widening conversions, truncate by definition
      let src = g.pick([tI8, tI16, tI32, tI64, tU8, tU16, tU32, tU64])
      tyName(t) & "(" & e(src) & ")"
    of 11:
      let src = g.pick([tU8, tU16, tU32, tU64])
      if bitWidth(src) == bitWidth(t): "cast[" & tyName(t) & "](" & e(src) & ")"
      else: tyName(t) & "(" & e(src) & ")"
    of 12, 13:     # `ck*` helpers use {.keepOverflowFlag.}; narrow ones are rare (see narrowOvf)
      if t == tI64 or g.narrowOvf:
        "ck" & g.pick(["add", "sub", "mul"]) & "_" & tyName(t) & "(" & e(t) & ", " & e(t) & ")"
      else: g.leaf(t)
    of 14:
      if t == tI32: "cast[int32](" & e(tU32) & ")"
      elif t == tI64: "cast[int64](" & e(tU64) & ")"
      else: g.leaf(t)
    of 15: "(not " & e(t) & ")"
    else: g.leaf(t)
  of tU16:
    case g.rng.rand(9)
    of 0..3: "(" & e(t) & " " & g.pick(["+", "-", "*", "xor", "and", "or"]) & " " & e(t) & ")"
    of 4: "(" & e(t) & " " & g.pick(["shl", "shr"]) & " (" & e(t) & " and 15'u16))"
    of 5: "(" & e(t) & " " & g.pick(["div", "mod"]) & " (" & e(t) & " or 1'u16))"
    of 6: "uint16(" & e(g.pick([tI8, tI16, tI32, tI64, tU8, tU32, tU64])) & ")"
    of 7: "cast[uint16](" & e(tI16) & ")"
    else: g.leaf(t)
  of tS, tB:
    g.leaf(t)
  of tU64, tU32, tU8:
    let s = suffix(t)
    let mask = $(bitWidth(t) - 1) & s
    case g.rng.rand(13)
    of 0..5:
      "(" & e(t) & " " & g.pick(["+", "-", "*", "xor", "and", "or"]) & " " & e(t) & ")"
    of 6: "(" & e(t) & " " & g.pick(["shl", "shr"]) & " (" & e(t) & " and " & mask & "))"
    of 7: "(" & e(t) & " " & g.pick(["div", "mod"]) & " (" & e(t) & " or 1" & s & "))"  # never zero
    of 8:
      case t
      of tU64: g.pick(["uint64(" & e(tU32) & ")", "uint64(" & e(tU8) & ")",
                       bitsOf(tF64, e(tF64)), "cast[uint64](" & e(tI64) & ")",
                       "uint64(" & e(g.pick([tI8, tI16, tI32, tI64, tU16])) & ")"])
      of tU32: g.pick(["uint32(" & e(tU64) & " and 0xffffffff'u64)", "uint32(" & e(tU8) & ")",
                       "uint32(" & e(g.pick([tI8, tI16, tI32, tI64, tU16])) & ")",
                       "cast[uint32](" & e(tI32) & ")", bitsOf(tF32, e(tF32))])
      else: g.pick(["uint8(" & e(tU64) & " and 255'u64)", "uint8(" & e(tU32) & " and 255'u32)"])
    of 9: "(not " & e(t) & ")"
    of 10: tyName(t) & "(ord(" & g.cond(depth - 1) & "))"
    else: g.leaf(t)
  of tF64:
    case g.rng.rand(15)
    of 0..4: "(" & e(t) & " " & g.pick(["+", "-", "*", "/"]) & " " & e(t) & ")"
    of 5: "(-(" & e(t) & "))"
    of 6: g.pick(["float64(" & e(tU32) & ")", "float64(" & e(tI32) & ")",
                  "float64(" & e(tI8) & ")", "float64(" & e(tI16) & ")", "float64(" & e(tU16) & ")",
                  "float64(" & e(tI64) & ")", "float64(" & e(tU64) & ")",
                  "float64(" & e(tF32) & ")"])
    of 7: "cast[float64](" & e(tU64) & ")"
    of 8: g.pick(["sqrt", "floor", "round", "trunc", "ceil", "abs"]) & "(" & e(t) & ")"
    of 9: g.pick(["min", "max"]) & "(" & e(t) & ", " & e(t) & ")"
    of 10: (if g.chance(0.3): "pow(" & e(t) & ", " & e(t) & ")" else: g.leaf(t))
    else: g.leaf(t)
  of tF32:
    case g.rng.rand(9)
    of 0..3: "(" & e(t) & " " & g.pick(["+", "-", "*", "/"]) & " " & e(t) & ")"
    of 4: g.pick(["float32(" & e(tF64) & ")", "float32(" & e(tU32) & ")",
                  "float32(" & e(tI32) & ")", "float32(" & e(tI16) & ")", "float32(" & e(tI64) & ")"])
    of 5: "cast[float32](" & e(tU32) & ")"
    of 6: "sqrt(" & e(t) & ")"
    else: g.leaf(t)
  of tObj:
    g.leaf(t)
  of tBool:
    case g.rng.rand(7)
    of 0..3:
      let ct = g.pick([tU64, tU32, tU8, tI32, tI64, tF64, tF32, tI8, tI16, tU16])
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

proc baseStmt(g: var Gen): Node =
  ## difffuzz's statements: `if`, `for`, assignments to scalars, `V` objects and `arr`.
  let depth = 3
  let roll = g.rng.rand(99)
  if roll < 10 and g.nest < 2:
    inc g.nest
    result = Node(line: "if " & g.cond(2) & ":", kids: g.stmts(1 + g.rng.rand(3)))
    if g.chance(0.5):
      result.hasElse = true
      result.elseKids = g.stmts(1 + g.rng.rand(2))
    dec g.nest
  elif roll < 16 and g.nest < 2:
    inc g.nest
    let lv = "k" & $g.loopVars.len
    g.loopVars.add lv
    inc g.loopDepth
    result = Node(line: "for " & lv & " in 0 ..< " & $(1 + g.rng.rand(4)) & ":",
                  kids: g.stmts(1 + g.rng.rand(3)))
    dec g.loopDepth
    discard g.loopVars.pop()
    dec g.nest
  elif roll < 24:
    result = Node(line: g.pick(["v", "w"]) & "." & g.pick(["x", "y"]) & " = " & g.expr(tF64, depth))
  elif roll < 28:
    result = Node(line: g.pick(["v", "w"]) & ".n = " & g.expr(tU32, depth))
  elif roll < 31:
    result = Node(line: g.pick(["v", "w"]) & " = V(x: " & g.expr(tF64, 2) & ", y: " &
                        g.expr(tF64, 2) & ", n: " & g.expr(tU32, 2) & ")")
  elif roll < 33:
    result = Node(line: g.pick(["v = w", "w = v"]))
  elif roll < 36:
    let c = g.callHelper(tObj, depth)
    result = Node(line: (if c.len > 0: g.pick(["v", "w"]) & " = " & c else: "v = w"))
  elif roll < 41:
    result = Node(line: "arr[(" & g.expr(tU64, 2) & ") and 7'u64] = " & g.expr(tU64, depth))
  else:
    let (n, t) = g.pick(g.vars)
    if n.startsWith("p"):                   # parameters are immutable
      result = Node(line: "a0 = " & g.expr(tU64, depth))
    else:
      result = Node(line: n & " = " & g.expr(t, depth))

proc extStmt(g: var Gen): Node =
  ## bfuzz's statements: case, while/break/continue, narrow ints,
  ## small/large objects, nested arrays, strings.
  let depth = 3
  let roll = g.rng.rand(99)
  if roll < 8 and g.nest < 2:
    inc g.nest
    let sel = if g.narrowCase: g.pick([tU8, tI8, tI16, tI32, tI64]) else: tObj  # tObj: `int` selector
    let s = if g.narrowCase: suffix(sel) else: ""
    result = Node(line: "case " & (if sel == tU8: "(" & g.expr(tU8, 2) & " and 7'u8)"
                                   elif sel == tObj: "(int(" & g.expr(g.pick([tI8, tI16, tI32, tU8]), 2) & ") and 7)"
                                   else: "(" & g.expr(sel, 2) & " and 7" & s & ")"))
    var arms = @["of 0" & s & ":", "of 1" & s & ", 2" & s & ":", "of 3" & s & " .. 5" & s & ":", "else:"]
    if g.chance(0.3): arms = @["of 6" & s & ":", "else:"]
    for a in arms: result.arms.add Node(line: a, kids: g.stmts(1 + g.rng.rand(2)))
    dec g.nest
  elif roll < 16 and g.nest < 2:
    inc g.nest
    inc g.loopDepth
    let wc = "wc" & $g.nest
    g.loopVars.add wc
    result = Node(prelude: wc & " = 0", line: "while " & wc & " < " & $(1 + g.rng.rand(5)) & ":",
                  bodyPre: @["inc " & wc], kids: g.stmts(1 + g.rng.rand(3)))
    discard g.loopVars.pop()
    dec g.loopDepth
    dec g.nest
  elif roll < 22 and g.loopDepth > 0:
    result = Node(line: "if " & g.cond(2) & ":", kids: @[Node(line: g.pick(["break", "continue"]))])
  elif roll < 34:
    let t = g.pick([tI8, tI16, tI32, tI64, tU16])
    let n = if t == tU16: "u16v" else: "i" & $bitWidth(t) & "v"
    result = Node(line: n & " = " & g.expr(t, depth))
  elif roll < 40:
    result = Node(line: g.pick(["s0", "s1"]) & "." & g.pick(["a = " & g.expr(tI16, depth),
                  "b = " & g.expr(tI8, depth), "c = " & g.expr(tF32, depth)]))
  elif roll < 46:
    let t = g.pick([tS, tB])
    let c = g.callHelper(t, depth)
    result = Node(line: (if c.len > 0: (if t == tS: g.pick(["s0", "s1"]) else: g.pick(["b0", "b1"])) & " = " & c
                         else: g.pick(["s0 = s1", "b1 = b0", "s1 = s0", "b0 = b1"])))
  elif roll < 52:
    result = Node(line: g.pick(["b0", "b1"]) & g.pick([".q[(" & g.expr(tU64, 2) & ") and 3'u64] = " & g.expr(tU64, depth),
                  ".d = " & g.expr(tF64, depth), ".e = " & g.expr(tI8, depth)]))
  elif roll < 60:
    result = Node(line: "mat[(" & g.expr(tU64, 2) & ") mod 3'u64][(" & g.expr(tU64, 2) & ") and 3'u64] = " &
                        g.expr(tI32, depth))
  elif roll < 64:
    result = Node(line: g.pick(["mat[0] = mat[2]", "mat[1][0] = mat[2][3]", "mat = mat2", "mat2 = mat",
                                "mat2[" & $g.rng.rand(2) & "] = mat[" & $g.rng.rand(2) & "]"]))
  elif roll < 80:
    let t = g.pick([tI8, tI16, tI32, tI64, tU8, tU16, tU32, tU64, tF64, tF32, tBool])
    var v = g.expr(t, 2)
    # NaN sign is unspecified (see bitsOf), so `$` must not see a NaN
    if t in {tF64, tF32}: v = "(if " & v & " != " & v & ": 0.0 else: float64(" & v & "))"
    result = Node(line: "if sb.len < 400:", kids: @[Node(line: g.pick([
      "sb.add $(" & v & ")", "sb = sb & $(" & v & ") & \",\"", "sb.add '" & g.pick(["x", "-", "7"]) & "'",
      "sb.add \"ab\" & $(" & v & ")"]))])
  else:
    result = g.baseStmt()

proc stmt(g: var Gen): Node =
  if g.chance(0.45): return g.extStmt()
  result = g.baseStmt()

proc stmts(g: var Gen; n: int): seq[Node] =
  for i in 0 ..< n: result.add g.stmt()

# ---- helpers and procs ----------------------------------------------------------

proc toU64(t: Ty; x: string): string =
  ## Every scalar as a uint64 that depends on all its bits.
  case t
  of tF64, tI64: bitsOf(t, x)
  of tS: "(uint64(cast[uint16](" & x & ".a)) xor (uint64(cast[uint8](" & x & ".b)) shl 16) xor (uint64(" &
         bitsOf(tF32, x & ".c") & ") shl 24))"
  of tB: "(" & x & ".q[0] xor " & x & ".q[3] xor " & bitsOf(tF64, x & ".d") & " xor uint64(cast[uint8](" & x & ".e)))"
  of tObj: "(" & bitsOf(tF64, x & ".x") & " xor uint64(" & x & ".n))"
  else: "uint64(" & bitsOf(t, x) & ")"

proc genHelper(g: var Gen; i: int): Helper =
  ## Helper `h<i>`: a fixed small signature, or 6..17 mixed parameters.
  let shapes = [(@[tF64, tF64], tF64), (@[tU64, tU32], tU64), (@[tObj, tF64], tObj),
                (@[tF32, tI32], tF32), (@[tF64, tObj, tU32], tObj), (@[tI32, tU32], tI32),
                (@[tS, tI16], tS), (@[tB, tF64], tB), (@[tS, tB, tI8], tU64), (@[tI8, tI16], tI16)]
  var (params, ret) = g.pick(shapes)
  var foldAll = false
  if g.chance(0.4):
    # many parameters, mixed int/float, often more than 8 floats (ABI: stack args)
    params = @[]
    let n = 6 + g.rng.rand(12)
    for j in 0 ..< n:
      params.add g.pick([tF64, tF64, tF32, tF64, tI8, tI16, tI32, tI64, tU8, tU16, tU32, tU64, tS, tB, tObj, tBool])
    ret = g.pick([tU64, tU64, tF64, tF32, tI32, tI8, tS, tB, tObj])
    foldAll = g.chance(0.7)
  result = Helper(name: "h" & $i, params: params, ret: ret)
  g.vars.setLen 0
  var decl: seq[string] = @[]
  var objParam = ""
  var folded: seq[string] = @[]
  for j, p in params:
    folded.add toU64(p, "q" & $j)
    if p == tS:
      decl.add "q" & $j & ": S"
      g.vars.add ("q" & $j & ".a", tI16)
      g.vars.add ("q" & $j & ".c", tF32)
    elif p == tB:
      decl.add "q" & $j & ": B"
      g.vars.add ("q" & $j & ".q[2]", tU64)
      g.vars.add ("q" & $j & ".d", tF64)
      g.vars.add ("q" & $j & ".e", tI8)
    elif p == tObj:
      decl.add "q" & $j & ": V"
      objParam = "q" & $j
    else:
      decl.add "q" & $j & ": " & tyName(p)
      g.vars.add ("q" & $j, p)
  var body: string
  # helpers see no `v`/`w`/`arr`: rename those leaves to the object param (or a literal)
  if objParam.len > 0:
    g.vars.add (objParam & ".x", tF64)
    g.vars.add (objParam & ".n", tU32)
  var mix = ""
  if foldAll:
    # every parameter reaches the result: a wrong ABI slot shows up
    var parts: seq[string] = @[]
    for j, a in folded: parts.add "(" & a & " * " & $(2 * j + 3) & "'u64)"
    mix = "(" & parts.join(" xor ") & ")"
    g.vars.add ("mixv", tU64)
  if ret == tObj:
    body = "V(x: " & g.expr(tF64, 2) & ", y: " & g.expr(tF64, 2) & ", n: " & g.expr(tU32, 2) & ")"
  elif ret == tS:
    body = "S(a: " & g.expr(tI16, 2) & ", b: " & g.expr(tI8, 2) & ", c: " & g.expr(tF32, 2) & ")"
  elif ret == tB:
    body = "B(q: [" & g.expr(tU64, 2) & ", " & g.expr(tU64, 1) & ", " & g.expr(tU64, 1) & ", " &
           g.expr(tU64, 2) & "], d: " & g.expr(tF64, 2) & ", e: " & g.expr(tI8, 2) & ")"
  else:
    body = g.expr(ret, 3)
  if foldAll:
    case ret
    of tU64: body = "(mixv xor " & body & ")"
    of tI8, tI16, tI32, tI64, tU8, tU16, tU32: body = "(" & tyName(ret) & "(mixv) xor " & body & ")"
    of tF64, tF32: body = "(" & body & " + " & tyName(ret) & "(mixv and 0xffff'u64))"
    of tS: body = "S(a: int16(mixv), b: int8(mixv shr 16), c: float32(mixv shr 40))"
    of tB: body = "B(q: [mixv, not mixv, mixv shr 3, 7'u64], d: float64(mixv and 0xfffff'u64), e: int8(mixv shr 8))"
    of tObj: body = "V(x: float64(mixv shr 11), y: cast[float64](mixv), n: uint32(mixv and 0xffffffff'u64))"
    else: discard
    body = "let mixv = " & mix & "\n  " & body
  result.decl = "proc " & result.name & "(" & decl.join("; ") & "): " & tyName(ret) & " =\n  " & body

proc genProc(g: var Gen; i: int): (seq[string], seq[Node], seq[string], string) =
  ## Test proc `t<i>`: its declarations, body, printed values and call in `main`.
  g.haveObjs = false
  g.vars.setLen 0
  for p in Params: g.vars.add p
  var head: seq[string] = @[]
  let locals = [tU64, tU64, tU32, tU8, tI32, tI64, tF64, tF64, tF32, tBool]
  var printed: seq[string] = @[]
  for j, t in locals:
    let n = "a" & $j
    let init = g.expr(t, 2)
    head.add "  var " & n & ": " & tyName(t) & " = " & init
    g.vars.add (n, t)
    printed.add bitsOf(t, n)
  head.add "  var v = V(x: " & g.expr(tF64, 1) & ", y: " & g.expr(tF64, 1) & ", n: " & g.expr(tU32, 1) & ")"
  head.add "  var w = V(x: " & g.expr(tF64, 1) & ", y: p1, n: p2)"
  var elems: seq[string] = @[]
  for k in 0 ..< 8: elems.add "p0 + " & $k & "'u64"
  head.add "  var arr: array[8, uint64] = [" & elems.join(", ") & "]"
  for (n, t) in Narrow:
    head.add "  var " & n & ": " & tyName(t) & " = " & g.expr(t, 2)
  head.add "  var s0 = S(a: " & g.expr(tI16, 1) & ", b: " & g.expr(tI8, 1) & ", c: " & g.expr(tF32, 1) & ")"
  head.add "  var s1 = S(a: int16(p4), b: int8(p2), c: p3)"
  head.add "  var b0 = B(q: [p0, p0 xor 1'u64, " & g.expr(tU64, 1) & ", 9'u64], d: p1, e: " & g.expr(tI8, 1) & ")"
  head.add "  var b1 = b0"
  head.add "  var mat: array[3, array[4, int32]] = [[p4, 1'i32, -2'i32, 3'i32], [" & g.expr(tI32, 1) &
           ", p4 * 3'i32, 0'i32, high(int32)], [low(int32), 7'i32, p4 - 1'i32, " & g.expr(tI32, 1) & "]]"
  head.add "  var mat2 = mat"
  head.add "  var sb = \"\""
  head.add "  var wc1 = 0"
  head.add "  var wc2 = 0"
  for (n, t) in Narrow:   # in scope only after the declarations above
    g.vars.add (n, t)
    printed.add bitsOf(t, n)
  g.haveObjs = true
  let body = g.stmts(6 + g.rng.rand(14))
  for f in ["v.x", "v.y", "w.x", "w.y"]: printed.add bitsOf(tF64, f)
  printed.add ["v.n", "w.n"]
  for j in 0 ..< 8: printed.add "arr[" & $j & "]"
  for o in ["s0", "s1"]:
    printed.add bitsOf(tI16, o & ".a")
    printed.add bitsOf(tI8, o & ".b")
    printed.add bitsOf(tF32, o & ".c")
  for o in ["b0", "b1"]:
    for j in 0 ..< 4: printed.add o & ".q[" & $j & "]"
    printed.add bitsOf(tF64, o & ".d")
    printed.add bitsOf(tI8, o & ".e")
  for m in ["mat", "mat2"]:
    for r in 0 ..< 3:
      for c in 0 ..< 4: printed.add bitsOf(tI32, m & "[" & $r & "][" & $c & "]")
  printed.add ["sb.len", "\"[\" & sb & \"]\""]
  let call = "t" & $i & "(" & g.lit(tU64) & ", " & g.lit(tF64) & ", " & g.lit(tU32) &
             ", " & g.lit(tF32) & ", " & g.lit(tI32) & ")"
  (head, body, printed, call)

proc generate(seed, nprocs: int): Program =
  ## The program for `seed`: six helpers and `nprocs` test procs.
  var g = Gen(rng: initRand(seed))
  g.narrowOvf = g.chance(0.12)
  g.narrowCase = g.chance(0.12)
  result.narrowOvf = g.narrowOvf
  for i in 0 ..< 6: g.helpers.add g.genHelper(i)
  result.helpers = g.helpers
  for i in 0 ..< nprocs:
    g.rng = initRand(seed * 1000 + i + 1)      # each proc reproducible on its own
    let (head, body, printed, call) = g.genProc(i)
    result.heads.add head
    result.bodies.add body
    result.printed.add printed
    result.calls.add call

# ---- rendering ------------------------------------------------------------------

proc render(n: Node; indent: int; res: var string) =
  let pad = repeat(' ', indent)
  if n.prelude.len > 0: res.add pad & n.prelude & "\n"
  res.add pad & n.line & "\n"
  for a in n.arms: render(a, indent, res)
  if n.line.endsWith(":"):
    for l in n.bodyPre: res.add pad & "  " & l & "\n"
    if n.kids.len == 0 and n.bodyPre.len == 0: res.add pad & "  discard\n"
    for k in n.kids: render(k, indent + 2, res)
    if n.hasElse:
      res.add pad & "else:\n"
      if n.elseKids.len == 0: res.add pad & "  discard\n"
      for k in n.elseKids: render(k, indent + 2, res)

proc render(p: Program; only: int = -1): string =
  ## The program's source; with `only >= 0`, just test proc `t<only>`.
  result = "# generated by nimony-fuzz/backends/bfuzz.nim\nimport std/[syncio, math]\n\n" &
           "type V = object\n  x, y: float64\n  n: uint32\n\n" &
           "type S = object\n  a: int16\n  b: int8\n  c: float32\n\n" &
           "type B = object\n  q: array[4, uint64]\n  d: float64\n  e: int8\n\n" &
           "proc sumMat(m: array[3, array[4, int32]]): int32 =\n  m[0][1] + m[1][2] * m[2][3] - m[2][0]\n\n"
  for t in (if p.narrowOvf: @[tI8, tI16, tI32, tI64] else: @[tI64]):
    let tn = tyName(t)
    for (op, o) in [("add", "+"), ("sub", "-"), ("mul", "*")]:
      result.add "proc ck" & op & "_" & tn & "(a, b: " & tn & "): " & tn & " =\n" &
        "  var r: " & tn & " = 0\n  var o = false\n  {.keepOverflowFlag.}:\n    r = a " & o & " b\n" &
        "    if overflowFlag(): o = true\n  if o: r = r xor 85" & suffix(t) & "\n  result = r\n\n"
  for h in p.helpers: result.add h.decl & "\n\n"
  for i in 0 ..< p.bodies.len:
    if only >= 0 and i != only: continue
    result.add "proc t" & $i & "(" & ParamDecl & ") =\n"
    for l in p.heads[i]: result.add l & "\n"
    for n in p.bodies[i]: render(n, 2, result)
    result.add "  echo \"t" & $i & " \", " & p.printed[i].join(", \" \", ") & "\n\n"
  result.add "proc main() =\n"
  for i in 0 ..< p.calls.len:
    if only >= 0 and i != only: continue
    result.add "  " & p.calls[i] & "\n"
  result.add "\nmain()\n"

# ---- running ----------------------------------------------------------------------

const RunWasm = currentSourcePath().parentDir / "run_wasm.js"  ## from tests/ithaqua

var nimony = "/home/ageralis/Projects/nimony/bin/nimony"
var flags = "-d:danger"
var workDir = "work"
var backends = @["c", "n", "l", "j", "w"]

type Run = tuple[compiled, ran: bool; output: string]

proc build(be, tag: string): (string, int) =
  ## Compile `<work>/<tag>/fz.nim` with backend `be`: (output, exit code).
  let dir = workDir / tag / be
  removeDir(dir)
  createDir(dir)
  execCmdEx("timeout 300 " & quoteShell(nimony) & " " & be & " " & flags &
            " --nimcache:" & quoteShell(dir) & " " & quoteShell(workDir / tag / "fz.nim"))

proc buildRun(be, tag: string): Run =
  var (outp, code) = build(be, tag)
  if code != 0 and ("cannot open" in outp or "deps.nif" in outp):
    (outp, code) = build(be, tag)       # known flake (report 08): retry once
  if code != 0: return (false, false, outp)
  var cmd = ""
  for f in walkDirRec(workDir / tag / be):
    let n = f.extractFilename
    case be
    of "j": (if n == "fz.js": cmd = "node " & quoteShell(f))
    of "w": (if n == "fz.wasm": cmd = "node " & quoteShell(RunWasm) & " " & quoteShell(f))
    else: (if n == "fz" and fpUserExec in getFilePermissions(f): cmd = quoteShell(f))
  if cmd.len == 0: return (false, false, "no executable produced\n" & outp)
  let (r, rc) = execCmdEx("timeout 20 " & cmd & " </dev/null")
  (true, rc == 0, (if rc == 0: r else: r & "\nexit code " & $rc))

proc runAll(src, tag: string; bes: seq[string]): Table[string, Run] =
  ## Build and run `src` with each backend in `bes`.
  createDir(workDir / tag)
  writeFile(workDir / tag / "fz.nim", src)
  for be in bes: result[be] = buildRun(be, tag)

proc firstDiff(a, b: string): int =
  ## The `t<i>` of the first output line that differs, or -1.
  let la = a.splitLines
  let lb = b.splitLines
  for i in 0 ..< max(la.len, lb.len):
    let x = if i < la.len: la[i] else: ""
    let y = if i < lb.len: lb[i] else: ""
    if x != y:
      let s = if x.startsWith("t"): x else: y
      if s.startsWith("t"):
        let sp = s.find(' ')
        if sp > 1:
          try: return parseInt(s[1 ..< sp]) except ValueError: discard
      return -1
  -1

proc classify(runs: Table[string, Run]; be: string): Verdict =
  ## Compare backend `be` against the C oracle.
  let c = runs["c"]
  if not c.compiled or not c.ran:
    return Verdict(outcome: invalid, detail: "C backend: " & c.output)
  let other = runs[be]
  if not other.compiled:
    # arkham/nifasm name the proc they failed in: `… in proc t7.0.fz…`.
    var bad = -1
    let k = other.output.find("in proc t")
    if k >= 0:
      var j = k + "in proc t".len
      var num = ""
      while j < other.output.len and other.output[j] in {'0'..'9'}:
        num.add other.output[j]; inc j
      if num.len > 0: bad = parseInt(num)
    return Verdict(outcome: compileFails, outC: c.output, outOther: other.output, detail: other.output, badProc: bad)
  if not other.ran:
    return Verdict(outcome: runFails, outC: c.output, outOther: other.output, badProc: firstDiff(c.output, other.output))
  if c.output != other.output:
    return Verdict(outcome: mismatch, outC: c.output, outOther: other.output, badProc: firstDiff(c.output, other.output))
  Verdict(outcome: okSame)

proc check(src, tag, be: string): Verdict =
  ## Build and classify `src` with C and `be` only (the reducer's test).
  classify(runAll(src, tag, @["c", be]), be)

proc normKey(s: string): string =
  ## The line that identifies a compile failure, without paths and numbers:
  ## the reducer keeps chasing the SAME failure, and findings dedupe on it.
  var key = s.strip
  for l in s.splitLines:
    if "warning" notin l and ("Error" in l or "error:" in l or "unsupported" in l or
                              "BUG" in l or "Assertion" in l):
      key = l.strip
      break
  for ch in key:
    if ch in {'0'..'9'}: (if result.len == 0 or result[^1] != '#': result.add '#')
    else: result.add ch
  let k = result.find("/home/")
  if k >= 0:
    var e = k
    while e < result.len and result[e] notin {' ', ':', ')', '('}: inc e
    result[k ..< e] = "<path>"
  let ip = result.find(" in proc t")
  if ip >= 0: result.setLen ip
  let ll = result.find(".ll:")
  if ll >= 0: result = result[ll + 4 .. ^1]
  if result.len > 160: result.setLen 160

# ---- reduction -----------------------------------------------------------------------

proc sameFailure(a, b: Verdict): bool =
  ## Same outcome and, for compile failures, the same error (the reducer's goal).
  if a.outcome != b.outcome: return false
  if a.outcome == compileFails: return normKey(a.detail) == normKey(b.detail)
  true

var budget = 150   ## max reducer test builds per finding

proc reduce(p: var Program; target: Verdict; only: int; tag, be: string): string =
  ## Delete statements (and unwrap `if`/`for`) while the failure persists.
  var tests = 0
  proc stillFails(p: Program): bool =
    inc tests
    if tests > budget: return false
    let r = check(render(p, only), tag, be)
    sameFailure(r, target)

  proc prune(p: var Program; list: var seq[Node]): bool =
    ## Delete or unwrap each statement of `list`, recursively; true if any went.
    result = false
    var i = 0
    while i < list.len:
      let saved = list[i]
      list.delete(i)
      if stillFails(p):
        result = true
        continue
      list.insert(saved, i)
      if saved.kids.len > 0:
        # unwrap: replace the compound statement by its body
        list.delete(i)
        for j, k in saved.kids: list.insert(k, i + j)
        if stillFails(p):
          result = true
          continue
        for j in 0 ..< saved.kids.len: list.delete(i)
        list.insert(saved, i)
        if prune(p, saved.kids): result = true
        if saved.hasElse and prune(p, saved.elseKids): result = true
      for a in saved.arms:
        if prune(p, a.kids): result = true
      inc i

  proc zeroInits(p: var Program; pi: int): bool =
    ## Replace each local's initializer in `t<pi>` by a trivial value of its type.
    result = false
    for li in 0 ..< p.heads[pi].len:
      let line = p.heads[pi][li]
      let colon = line.find(": ")
      let eq = line.find(" = ")
      if not line.startsWith("  var ") or eq < 0: continue
      var simple = ""
      if line.startsWith("  var v = ") or line.startsWith("  var w = "):
        simple = line[0 ..< eq] & " = V(x: 0.0, y: 0.0, n: 0'u32)"
      elif colon > 0 and colon < eq:
        let tn = line.substr(colon + 2, eq - 1)
        let zero = case tn
          of "uint64": "0'u64"
          of "uint32": "0'u32"
          of "uint8": "0'u8"
          of "int32": "0'i32"
          of "int64": "0'i64"
          of "float64": "0.0"
          of "float32": "0.0'f32"
          of "bool": "false"
          of "int8": "0'i8"
          of "int16": "0'i16"
          of "uint16": "0'u16"
          else: ""
        if zero.len > 0: simple = line[0 ..< eq] & " = " & zero
      if simple.len == 0 or simple == line: continue
      p.heads[pi][li] = simple
      if stillFails(p): result = true
      else: p.heads[pi][li] = line

  # Print only the values that differ: everything else printed is a call (and
  # a live range) the miscompile may not need.
  if only >= 0 and target.outcome == mismatch:
    let la = target.outC.splitLines
    let lb = target.outOther.splitLines
    for k in 0 ..< min(la.len, lb.len):
      if la[k] != lb[k] and la[k].startsWith("t" & $only & " "):
        let xa = la[k].split(' ')
        let xb = lb[k].split(' ')
        var keep: seq[string] = @[]
        for c in 1 ..< min(xa.len, xb.len):
          if xa[c] != xb[c] and c - 1 < p.printed[only].len:
            keep.add p.printed[only][c - 1]
        if keep.len > 0:
          let saved = p.printed[only]
          p.printed[only] = keep
          let r = check(render(p, only), tag, be)
          inc tests
          if r.outcome != mismatch: p.printed[only] = saved
        break

  var changed = true
  while changed and tests <= budget:
    changed = false
    for pi in 0 ..< p.bodies.len:
      if only >= 0 and pi != only: continue
      if prune(p, p.bodies[pi]): changed = true
      if zeroInits(p, pi): changed = true
  # Last, a plain line-level pass over the rendered text: it can delete what the
  # structured passes cannot (unused declarations, whole helpers), which is
  # often what pins down a register-allocation dependent failure.
  var lines = render(p, only).splitLines
  var i = 0
  while i < lines.len and tests <= budget:
    let l = lines[i]
    # keep the skeleton: imports, type fields, test procs, their echo and calls
    let keep = l.len == 0 or l.startsWith("import") or l.startsWith("type") or
               l.startsWith("  a: int16") or l.startsWith("  b: int8") or l.startsWith("  c: float32") or
               l.startsWith("  q: array") or l.startsWith("  d: float64") or l.startsWith("  e: int8") or
               l.startsWith("  x, y") or l.startsWith("  n: uint32") or
               l.startsWith("proc t") or l.startsWith("proc main") or
               l.startsWith("main()") or l.startsWith("  echo") or
               (l.startsWith("  t") and "(" in l)
    if not keep:
      var cand = lines
      cand.delete(i)
      inc tests
      if sameFailure(check(cand.join("\n"), tag, be), target):
        lines = cand
        continue
    inc i
  lines.join("\n")

# ---- driver ------------------------------------------------------------------------

proc main() =
  var first = int(epochTime() * 1000) mod 1_000_000
  var count = 10
  var nprocs = 12
  var outDir = "bfuzz.out"
  var doReduce = true
  var timeLimit = 0.0
  var maxReduce = 3
  var emit = false
  for kind, key, val in getopt():
    case key
    of "seed": first = parseInt(val)
    of "count": count = parseInt(val)
    of "procs": nprocs = parseInt(val)
    of "flags": flags = val
    of "nimony": nimony = val
    of "out": outDir = val
    of "work": workDir = val
    of "budget": budget = parseInt(val)
    of "noreduce": doReduce = false
    of "time": timeLimit = parseFloat(val)
    of "backends": backends = val.split(',')
    of "maxreduce": maxReduce = parseInt(val)
    of "emit": emit = true
    else: quit "unknown option: " & key
  if emit:
    echo render(generate(first, nprocs)); return
  nimony = absolutePath(nimony)
  workDir = absolutePath(workDir)
  createDir(outDir)
  if "c" notin backends: backends.insert("c", 0)    # the oracle always runs
  var others: seq[string] = @[]
  for be in backends:
    if be != "c": others.add be
  let t0 = epochTime()
  let cpu0 = cpuTime()
  var found, invalidCount, programs = 0
  var perBe = initCountTable[string]()
  var seen = initCountTable[string]()    # findings per signature
  let events = open(outDir / "events.csv", fmAppend)
  events.writeLine "time_s,programs,backend,outcome,signature,seed,file"
  for k in 0 ..< count:
    if timeLimit > 0 and epochTime() - t0 > timeLimit: break
    let seed = first + k
    var p = generate(seed, nprocs)
    let tag = "s" & $seed
    let src = render(p)
    let runs = runAll(src, tag, backends)
    inc programs
    if not runs["c"].compiled or not runs["c"].ran:
      inc invalidCount
      echo &"seed {seed}: INVALID (generator bug; C side failed)"
      writeFile(outDir / &"invalid_{seed}.nim", src)
      writeFile(outDir / &"invalid_{seed}.txt", runs["c"].output)
      continue
    var verdicts = initTable[string, Verdict]()
    for be in others: verdicts[be] = classify(runs, be)
    # C suspect: every other backend ran, they all agree, and C alone differs
    var cSuspect = others.len >= 2
    for be in others:
      if verdicts[be].outcome != mismatch or runs[be].output != runs[others[0]].output: cSuspect = false
    var line = &"seed {seed}:"
    for be in (if cSuspect: @[others[0]] else: others):
      let r = verdicts[be]
      if r.outcome == okSame: continue
      let who = if cSuspect: "c" else: be
      let sig = who & ":" & $r.outcome & ":" & (if r.outcome == compileFails: normKey(r.detail) else: "")
      seen.inc sig
      perBe.inc who
      inc found
      line.add &" [{who} {r.outcome} t{r.badProc}]"
      let base = outDir / &"{who}_{r.outcome}_{seed}"
      writeFile(base & ".nim", src)
      writeFile(base & ".c.txt", r.outC)
      writeFile(base & "." & be & ".txt", (if r.outcome == compileFails: r.detail else: r.outOther))
      let csig = sig.replace("\"", "'").replace(",", ";")
      events.writeLine &"{int(epochTime() - t0)},{programs},{who},{r.outcome},{csig},{seed},{base}.nim"
      events.flushFile()
      # a compile error's signature names one bug; all mismatches share one signature
      if doReduce and seen[sig] <= (if r.outcome == compileFails: 1 else: maxReduce):
        var only = r.badProc
        # reduce `t<badProc>` alone only if it fails without the other procs
        if only >= 0 and not sameFailure(check(render(p, only), tag, be), r): only = -1
        var pc = p
        let reduced = reduce(pc, r, only, tag, be)
        let rr = check(reduced, tag, be)
        writeFile(base & ".reduced.nim", reduced)
        writeFile(base & ".reduced.c.txt", rr.outC)
        writeFile(base & ".reduced." & be & ".txt", (if rr.outcome == compileFails: rr.detail else: rr.outOther))
        echo &"  reduced to {reduced.countLines} lines: {base}.reduced.nim"
    if line.endsWith(":"): line.add " same"
    removeDir(workDir / tag)
    echo &"{int(epochTime() - t0)}s ", line
  events.close()
  echo &"{programs} programs, {found} findings, {invalidCount} invalid (generator), " &
       &"wall {int(epochTime() - t0)}s, driver cpu {cpuTime() - cpu0:.1f}s — {outDir}"
  for be, n in perBe: echo &"  {be}: {n} raw findings"
  for sig, n in seen: echo &"  {n}x {sig}"

main()
