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

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables, sequtils]

type
  K = enum
    eLit, eVar, eCall, eAdd, eIfx, eTryx, eBlkx, eLen, eStr,  # int expressions (eStr: only in O(b: ..))
    cAnd, cOr, cNot, cLt, cSeq,                                # conditions (evaluate to 0/1)
    sEcho, sEchoE, sAsgn, sSAsgn, sRaise, sReraise, sIf, sFor, sBlock, sBreak, sCont,
    sRet, sTry, sDefer, sCase, sLet, sObj,
    xBr, xProc, xProg
  N = ref object
    ## xBr: a branch (stmts `a` + optional tail `e[0]`: expr or sRaise). Except
    ## arms are xBr with s=kind, t=`as` name, u=token; case branches carry vs.
    ## sIf: a=[then, else]; sCase: a=[of.., else], s=string var or e[0]=int
    ## selector; sTry: a=[body, arms..], f=finally; sLet: e[0] or a[0]=sIf/sCase/sTry.
    k: K
    s, t, u: string
    v: int
    vs: seq[string]
    e, a: seq[N]
    f: N
  C = object  ## generator context
    ints, mut, strs, hs: seq[string]
    loops: seq[(bool, string)]  ## (is a `for`, id/label)
    helper, arm, inexpr, indefer, nofinraise, nofinjump: bool
  Jump = object of CatchableError  ## raise/break/continue/return in flight
    k: K
    s: string
    v: int
  Big = object of CatchableError
  Env = ref object
    i: Table[string, int]
    s: Table[string, string]

const
  Codes = ["ValueError", "IOError", "OverflowError", "KeyError", "RangeError", "SyntaxError"]
  Strs = ["", "a", "ab", "abc", "abd", "abcd", "abce", "b", "ba", "bab", "xyz", "xy", "hello",
          "help", "helpme", "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaab", "Abc", "abc ",
          "zz", "z", "qwertyuiop", "qwertyuiopa", "0", "01", "10"]
  Cfgs = [("c", "c"), ("opt", "c --opt:speed"), ("n", "n")]

var
  r: Rand
  rd: bool          ## ref-exception domain
  ntok, nnm: int
  allow = ""

# ---- generator ----------------------------------------------------------------

proc ch(p: float): bool = r.rand(1.0) < p
proc tk(pf = "t"): string = inc ntok; pf & $ntok
proc nm(pf: string): string = inc nnm; pf & $nnm
proc nn(k: K; e: varargs[N]): N = N(k: k, e: @e)
proc lit(v: int): N = N(k: eLit, v: v)
proc exc(): string =
  if rd: r.sample(["E1", "E2", "E2", "E3", "E3"]) & ":" & tk("m") else: r.sample(Codes)

proc cond(c: C; d: int): N
proc stmts(c: C; d, n: int): seq[N]

proc ex(c: C; d: int): N =
  if d <= 0 or ch(0.3):
    return (if c.ints.len > 0 and ch(0.6): N(k: eVar, s: r.sample(c.ints)) else: lit(r.rand(9)))
  let x = r.rand(1.0)
  if x < 0.30 and c.hs.len > 0: N(k: eCall, s: r.sample(c.hs), e: @[ex(c, d-1)])
  elif x < 0.45: nn(eAdd, ex(c, d-1), ex(c, d-1))
  elif x < 0.58: nn(eIfx, cond(c, d-1), ex(c, d-1), ex(c, d-1))
  elif x < 0.70 and not (rd and '2' notin allow): nn(eTryx, ex(c, d-1), ex(c, d-1))
  elif x < 0.80: N(k: eBlkx, s: tk("b"), e: @[ex(c, d-1)])
  elif x < 0.88 and c.strs.len > 0: N(k: eLen, s: r.sample(c.strs))
  else: nn(eAdd, ex(c, d-1), lit(r.rand(5)))

proc cond(c: C; d: int): N =
  let x = r.rand(1.0)
  if d > 0 and x < 0.35: nn(r.sample([cAnd, cOr]), cond(c, d-1), cond(c, d-1))
  elif d > 0 and x < 0.42: nn(cNot, cond(c, d-1))
  elif x < 0.5 and c.strs.len > 0: N(k: cSeq, s: r.sample(c.strs), t: r.sample(Strs))
  else: nn(cLt, ex(c, d-1), ex(c, d-1))

proc branch(c: C; d: int; mayRaise = true): N =
  ## A branch of an expression: optional statements, then a value (or a raise).
  result = N(k: xBr)
  if ch(0.5):
    var s = c
    s.inexpr = true; s.loops = @[]; s.arm = false
    result.a = stmts(s, d-1, r.rand(1..2))
  result.e = @[if mayRaise and '1' in allow and ch(0.1): N(k: sRaise, s: exc()) else: ex(c, 2)]

proc strbrs(mk: proc(): N): seq[N] =
  var pool = @Strs
  r.shuffle(pool)
  for i in 0 ..< r.rand(1 .. (if ch(0.3): 10 else: 3)):
    let k = min(r.rand(1..3), pool.len)
    if k == 0: break
    let b = mk()
    b.vs = pool[0 ..< k]
    pool = pool[k .. ^1]
    result.add b

proc arms(mk: proc(): N): seq[N] =
  var ks: seq[string]
  if rd:
    ks = @["E1", "E2", "E3"]
    r.shuffle(ks)
    ks.setLen r.rand(0..3)
    if ch(0.3): ks.add "all"
  elif ch(0.8): ks = @[r.sample(["ec", "all"])]
  for kd in ks:
    let b = mk()
    b.s = kd
    b.t = if kd != "all" and ch(0.6): nm("e") else: ""
    b.u = tk("x")
    result.add b

proc mexpr(c: C; d: int; s: N) =
  ## The value of `let`: a plain expression or a multi-line if/case/try.
  let x = r.rand(1.0)
  if x < 0.2: s.e = @[ex(c, 3)]
  elif x < 0.4: s.a = @[N(k: sIf, e: @[cond(c, 2)], a: @[branch(c, d), branch(c, d)])]
  elif x < 0.55:
    var vals = toSeq(0..5)
    r.shuffle(vals)
    let n = N(k: sCase, e: @[ex(c, 2)])
    for i in 0 ..< r.rand(1..3):
      let k = r.rand(1..2)
      let b = branch(c, d)
      b.vs = vals[0 ..< k].mapIt($it)
      vals = vals[k .. ^1]
      n.a.add b
    n.a.add branch(c, d)
    s.a = @[n]
  elif (x < 0.7 and c.strs.len > 0) or (rd and '2' notin allow):
    if c.strs.len == 0: s.e = @[ex(c, 3)]
    else:
      s.a = @[N(k: sCase, s: r.sample(c.strs), a: strbrs(proc(): N = branch(c, d)) & branch(c, d))]
  else:
    let n = N(k: sTry, a: @[branch(c, d, false)] & arms(proc(): N = branch(c, d)))
    if ch(0.4) or n.a.len == 1:
      var f = c
      f.inexpr = true; f.loops = @[]; f.arm = false; f.indefer = true
      n.f = N(k: xBr, a: stmts(f, d-1, r.rand(1..2)))
    s.a = @[n]

proc stmt(c: C; d: int): N =
  let x = r.rand(1.0)
  let nojump = c.indefer or c.inexpr or c.nofinjump
  if d <= 0 or x < 0.12: N(k: sEcho, s: tk())
  elif x < 0.20: N(k: sEchoE, s: tk(), e: @[ex(c, 3)])
  elif x < 0.25 and c.mut.len > 0: N(k: sAsgn, s: r.sample(c.mut), e: @[ex(c, 3)])
  elif x < 0.28 and c.strs.len > 0 and not c.indefer:
    N(k: sSAsgn, s: r.sample(c.strs), t: r.sample(Strs))
  elif x < 0.35 and not c.indefer and not c.nofinraise: N(k: sRaise, s: exc())
  elif x < 0.37 and c.arm and not c.indefer: N(k: sReraise)
  elif x < 0.45:
    N(k: sIf, e: @[cond(c, 2)], a: @[N(k: xBr, a: stmts(c, d-1, r.rand(1..3))),
                                     N(k: xBr, a: stmts(c, d-1, r.rand(0..2)))])
  elif x < 0.52:
    let iv = nm("i")
    let id = nm("L")
    var s = c
    s.ints.add iv; s.loops.add (true, id); s.arm = false
    N(k: sFor, s: iv, t: id, v: r.rand(3), a: stmts(s, d-1, r.rand(1..4)))
  elif x < 0.56:
    let lab = nm("B")
    var s = c
    s.loops.add (false, lab)
    N(k: sBlock, s: lab, a: stmts(s, d-1, r.rand(1..3)))
  elif x < 0.62 and c.loops.len > 0 and not nojump:
    let inner = c.loops[^1]
    let lps = c.loops.filterIt(it[0])
    let bls = c.loops.filterIt(not it[0])
    if lps.len > 0 and ch(0.35): N(k: sCont)
    elif inner[0] and ch(0.5): N(k: sBreak, s: inner[1])
    elif bls.len > 0:
      let b = r.sample(bls)[1]
      N(k: sBreak, s: b, t: b)
    elif inner[0]: N(k: sBreak, s: inner[1])
    else: N(k: sEcho, s: tk())
  elif x < 0.66 and not nojump:
    N(k: sRet, e: (if c.helper: @[ex(c, 2)] else: @[]))
  elif x < 0.78 and not c.indefer:
    var b = c
    b.arm = false
    var a = c
    a.arm = true
    let n = N(k: sTry, a: @[N(k: xBr, a: stmts(b, d-1, r.rand(1..4)))] &
                          arms(proc(): N = N(k: xBr, a: stmts(a, d-1, r.rand(0..2)))))
    if ch(0.5) or n.a.len == 1:
      if '4' notin allow: b.hs = @[]; b.nofinraise = true
      if '5' notin allow: b.nofinjump = true
      n.f = N(k: xBr, a: stmts(b, d-1, r.rand(1..3)))
    n
  elif x < 0.83 and not c.indefer and not (c.inexpr and '3' notin allow):
    var s = c
    s.indefer = true; s.arm = false
    if '4' notin allow: s.hs = @[]
    N(k: sDefer, a: stmts(s, d-1, r.rand(1..2)))
  elif x < 0.89 and c.strs.len > 0:
    N(k: sCase, s: r.sample(c.strs),
      a: strbrs(proc(): N = N(k: xBr, a: stmts(c, d-1, r.rand(1..2)))) &
         N(k: xBr, a: stmts(c, d-1, r.rand(0..2))))
  elif x < 0.95:
    let n = N(k: sLet, s: tk(), t: nm("l"))
    mexpr(c, d-1, n)
    n
  else:
    var fs = @["a", "b", "c", "pk"]
    r.shuffle(fs)
    fs.setLen r.rand(0..3)
    let n = N(k: sObj, s: tk(), t: nm("o"))
    for f in ["a", "b", "c", "pk"]:
      if f in fs:
        n.vs.add f
        n.e.add(if f == "b": N(k: eStr, s: r.sample(Strs[0..11])) else: ex(c, 2))
    n

proc stmts(c: C; d, n: int): seq[N] =
  for i in 0 ..< n: result.add stmt(c, d)

proc gen(seed: int): N =
  r = initRand(seed)
  rd = ch(0.35)
  ntok = 0; nnm = 0
  result = N(k: xProg)
  var hs: seq[string]
  for i in 0 ..< r.rand(1..4):
    let c = C(ints: @["x", "h"], mut: @["h"], hs: hs, helper: true)
    result.a.add N(k: xProc, s: "f" & $i, a: stmts(c, 2, r.rand(1..3)), e: @[ex(c, 2)])
    hs.add "f" & $i
  for i in 0 ..< r.rand(2..5):
    let c = C(ints: @["v0", "v1"], mut: @["v0", "v1"], strs: @["s0", "s1"], hs: hs)
    result.a.add N(k: xProc, s: "t" & $i, a: stmts(c, 3, r.rand(2..5)), t: r.sample(Strs), u: r.sample(Strs))

# ---- rendering ------------------------------------------------------------------

proc q(s: string): string = '"' & s & '"'
proc rexc(x: string): string =
  let i = x.find(':')
  if i < 0: x else: x[0 ..< i] & "(msg: " & q(x[i+1 .. ^1]) & ")"

proc rx(e: N): string =
  template x(i: int): string = rx(e.e[i])
  case e.k
  of eLit: $e.v
  of eVar: e.s
  of eCall: e.s & "(" & x(0) & ")"
  of eAdd: "((" & x(0) & " + " & x(1) & ") and 1023)"
  of eIfx: "(if " & x(0) & ": " & x(1) & " else: " & x(2) & ")"
  of eTryx: "(try: " & x(0) & " except: " & x(1) & ")"
  of eBlkx: "(block: (echo " & q(e.s) & "; " & x(0) & "))"
  of eLen: e.s & ".len"
  of eStr: q(e.s)
  of cAnd: "(" & x(0) & " and " & x(1) & ")"
  of cOr: "(" & x(0) & " or " & x(1) & ")"
  of cNot: "(not " & x(0) & ")"
  of cLt: "(" & x(0) & " < " & x(1) & ")"
  of cSeq: "(" & e.s & " == " & q(e.t) & ")"
  else: "?"

proc rs(s: N; ind: int; o: var seq[string])

proc rb(b: N; ind: int; o: var seq[string]; dis = true) =
  if b.a.len + b.e.len == 0 and dis: o.add spaces(ind) & "discard"
  for x in b.a: rs(x, ind, o)
  if b.e.len > 0:
    o.add spaces(ind) & (if b.e[0].k == sRaise: "raise " & rexc(b.e[0].s) else: rx(b.e[0]))

proc rs(s: N; ind: int; o: var seq[string]) =
  let p = spaces(ind)
  case s.k
  of sEcho: o.add p & "echo " & q(s.s)
  of sEchoE: o.add p & "echo " & q(s.s & " ") & " & $(" & rx(s.e[0]) & ")"
  of sAsgn: o.add p & s.s & " = " & rx(s.e[0])
  of sSAsgn: o.add p & s.s & " = " & q(s.t)
  of sRaise: o.add p & "raise " & rexc(s.s)
  of sReraise: o.add p & "raise"
  of sIf:
    o.add p & "if " & rx(s.e[0]) & ":"
    rb(s.a[0], ind+2, o)
    if s.a[1].a.len + s.a[1].e.len > 0:
      o.add p & "else:"
      rb(s.a[1], ind+2, o)
  of sFor:
    o.add p & &"for {s.s} in 0..<{s.v}:"
    rb(s, ind+2, o)
  of sBlock:
    o.add p & "block " & s.s & ":"
    rb(s, ind+2, o)
  of sDefer:
    o.add p & "defer:"
    rb(s, ind+2, o)
  of sBreak: o.add p & strip("break " & s.t)
  of sCont: o.add p & "continue"
  of sRet: o.add p & "return" & (if s.e.len > 0: " " & rx(s.e[0]) else: "")
  of sTry:
    o.add p & "try:"
    rb(s.a[0], ind+2, o)
    for a in s.a[1 .. ^1]:
      let h = case a.s
        of "all": "except"
        of "ec": "except ErrorCode"
        else: "except " & a.s
      o.add p & h & (if a.t != "": " as " & a.t else: "") & ":"
      o.add p & "  echo " & (if a.t == "": q(a.u) elif rd: q(a.u & " ") & ", " & a.t & ".msg"
                             else: q(a.u & " ") & ", " & a.t)
      rb(a, ind+2, o, false)
    if s.f != nil:
      o.add p & "finally:"
      rb(s.f, ind+2, o)
  of sCase:
    o.add p & "case " & (if s.s != "": s.s else: rx(s.e[0]))
    for b in s.a[0 .. ^2]:
      o.add p & "of " & b.vs.mapIt(if s.s != "": q(it) else: it).join(", ") & ":"
      rb(b, ind+2, o)
    o.add p & "else:"
    rb(s.a[^1], ind+2, o)
  of sLet:
    if s.e.len > 0: o.add p & "let " & s.t & " = " & rx(s.e[0])
    else:
      let k = o.len
      rs(s.a[0], ind+2, o)
      o[k] = p & "let " & s.t & " = " & o[k].strip
    o.add p & "echo " & q(s.s & " ") & ", " & s.t
  of sObj:
    var fs: seq[string]
    for i, f in s.vs:
      fs.add(case f
        of "b": "b: " & q(s.e[i].s)
        of "pk": "p: P(k: " & rx(s.e[i]) & ")"
        else: f & ": " & rx(s.e[i]))
    let n = s.t
    o.add p & "let " & n & " = O(" & fs.join(", ") & ")"
    o.add p & "echo " & q(s.s & " ") & ", " & [n & ".a", n & ".b", n & ".c", n & ".p.k"].join(", \" \", ")
  else: discard

proc render(p: N): string =
  var o = @["import std/syncio", "", "type", "  E1 = ref object of Exception",
            "  E2 = ref object of E1", "  E3 = ref object of E1", "  P = object", "    k: int = 3",
            "  O = object", "    a: int = 5", "    b: string = \"xy\"", "    c: int", "    p: P", ""]
  let ra = if rd: "{.raises: E1.}" else: "{.raises.}"
  for x in p.a:
    if x.s[0] == 'f':
      o.add &"proc {x.s}(x: int): int {ra} ="
      o.add "  var h = x"
      rb(N(k: xBr, a: x.a), 2, o)
      o.add "  return " & rx(x.e[0])
    else:
      o.add &"proc {x.s}() {ra} ="
      o.add ["  var v0 = 1", "  var v1 = 2", "  var s0 = " & q(x.t), "  var s1 = " & q(x.u)]
      rb(x, 2, o)
    o.add ""
  for x in p.a:
    if x.s[0] == 't':
      o.add(if rd: "try: " & x.s & "() except E1 as e: echo \"U \", e.msg"
            else: "try: " & x.s & "() except ErrorCode as e: echo \"U \", e")
  o.join("\n") & "\n"

# ---- interpreter: the expected trace ----------------------------------------------

var
  outp: seq[string]
  steps: int
  procs: Table[string, N]

proc emit(s: string) =
  outp.add s
  if outp.len > 3000: raise newException(Big, "too much output")
proc tick() =
  inc steps
  if steps > 200_000: raise newException(Big, "too many steps")
proc jump(k: K; s = ""; v = 0) = raise (ref Jump)(k: k, s: s, v: v)
proc msg(x: string): string = x.split(':')[^1]  ## ref: the msg; ErrorCode: its name

proc blk(xs: seq[N]; env: Env; cur: string)
proc sel(s: N; env: Env; cur: string): int

proc call(name: string; a: int): int =
  let h = procs[name]
  let env = Env()
  env.i["x"] = a; env.i["h"] = a
  try: blk(h.a & N(k: sRet, e: h.e), env, "")  # the trailing return is in the scope of any defer
  except Jump as j:
    if j.k != sRet: raise
    return j.v

proc ev(e: N; env: Env): int =
  tick()
  template x(i: int): int = ev(e.e[i], env)
  case e.k
  of eLit: e.v
  of eVar: env.i[e.s]
  of eCall: call(e.s, x(0))
  of eAdd: (let a = x(0); (a + x(1)) and 1023)
  of eIfx: (if x(0) != 0: x(1) else: x(2))
  of eTryx: (try: x(0) except Jump: x(1))
  of eBlkx: (emit e.s; x(0))
  of eLen: env.s[e.s].len
  of cAnd: ord(x(0) != 0 and x(1) != 0)
  of cOr: ord(x(0) != 0 or x(1) != 0)
  of cNot: ord(x(0) == 0)
  of cLt: (let a = x(0); ord(a < x(1)))
  of cSeq: ord(env.s[e.s] == e.t)
  else: raise newException(ValueError, "not an expression")

proc br(b: N; env: Env; cur: string): int =
  blk(b.a, env, cur)
  if b.e.len == 0: 0
  elif b.e[0].k == sRaise: (jump(sRaise, b.e[0].s); 0)
  else: ev(b.e[0], env)

proc dotry(s: N; env: Env; cur: string): int =
  var p: ref Jump
  try: result = br(s.a[0], env, cur)
  except Jump as j:
    var arm: N
    if j.k == sRaise:
      for a in s.a[1 .. ^1]:
        if a.s in ["all", "ec", "E1"] or a.s == j.s.split(':')[0]:
          arm = a
          break
    if arm == nil: p = j
    else:
      try:
        emit arm.u & (if arm.t != "": " " & msg(j.s) else: "")
        result = br(arm, env, j.s)
      except Jump as j2: p = j2
  if s.f != nil: blk(s.f.a, env, cur)  # a jump out of the finally replaces p
  if p != nil: raise p

proc sel(s: N; env: Env; cur: string): int =
  case s.k
  of sIf: br(s.a[if ev(s.e[0], env) != 0: 0 else: 1], env, cur)
  of sCase:
    let v = if s.s != "": env.s[s.s] else: $ev(s.e[0], env)
    for b in s.a[0 .. ^2]:
      if v in b.vs: return br(b, env, cur)
    br(s.a[^1], env, cur)
  else: dotry(s, env, cur)

proc st(s: N; env: Env; cur: string) =
  tick()
  case s.k
  of sEcho: emit s.s
  of sEchoE: emit s.s & " " & $ev(s.e[0], env)
  of sAsgn: env.i[s.s] = ev(s.e[0], env)
  of sSAsgn: env.s[s.s] = s.t
  of sRaise: jump(sRaise, s.s)
  of sReraise: jump(sRaise, cur)
  of sIf, sCase, sTry: discard sel(s, env, cur)
  of sFor:
    for i in 0 ..< s.v:
      env.i[s.s] = i
      try: blk(s.a, env, cur)
      except Jump as j:
        if j.k == sCont: continue
        if j.k == sBreak and j.s == s.t: break
        raise
  of sBlock:
    try: blk(s.a, env, cur)
    except Jump as j:
      if j.k != sBreak or j.s != s.s: raise
  of sBreak: jump(sBreak, s.s)
  of sCont: jump(sCont)
  of sRet: jump(sRet, v = (if s.e.len > 0: ev(s.e[0], env) else: 0))
  of sLet: emit s.s & " " & $(if s.e.len > 0: ev(s.e[0], env) else: sel(s.a[0], env, cur))
  of sObj:
    var a = 5
    var b = "xy"
    var c = 0
    var k = 3
    for i, f in s.vs:
      case f
      of "a": a = ev(s.e[i], env)
      of "b": b = s.e[i].s
      of "c": c = ev(s.e[i], env)
      else: k = ev(s.e[i], env)
    emit &"{s.s} {a} {b} {c} {k}"
  else: raise newException(ValueError, "not a statement")

proc blk(xs: seq[N]; env: Env; cur: string) =
  for i, s in xs:
    if s.k == sDefer:  # the rest of the scope is the try body, the defer its finally
      var p: ref Jump
      try: blk(xs[i+1 .. ^1], env, cur)
      except Jump as j: p = j
      blk(s.a, env, cur)
      if p != nil: raise p
      return
    st(s, env, cur)

proc expected(p: N): string =
  outp.setLen 0
  steps = 0
  procs.clear
  for x in p.a: procs[x.s] = x
  for t in p.a:
    if t.s[0] != 't': continue
    let env = Env()
    env.i["v0"] = 1; env.i["v1"] = 2; env.s["s0"] = t.t; env.s["s1"] = t.u
    try: blk(t.a, env, "")
    except Jump as j:
      if j.k == sRaise: emit "U " & msg(j.s)
  outp.mapIt(it & "\n").join

proc make(seed: int): N =
  for salt in 0 .. 999:
    result = gen(seed * 1000 + salt)
    try:
      discard expected(result)
      return
    except Big: discard

# ---- oracle ---------------------------------------------------------------------

var
  nimony = getAppDir() / "../../nimony/bin/nimony"
  work = getAppDir() / "work"
  budget = 300
  got = ""  ## output of the last program run

proc errKey(o: string): string =
  ## The first error line, paths dropped and numbers collapsed, so the reducer
  ## keeps chasing the same failure.
  var l = ""
  for x in o.splitLines:
    if "Error" in x or "error:" in x or "Bug" in x or "BUG" in x:
      l = x
      break
  if l == "": l = (o.strip.splitLines & @["?"])[^1]
  for w in l.splitWhitespace:
    for c in (if '/' in w: w.extractFilename else: w) & " ":
      if c notin Digits: result.add c
      elif result.len == 0 or result[^1] != 'N': result.add 'N'
  result = result.strip
  if result.len > 110: result.setLen 110

proc verdict(p: N; cfg: string): string =
  ## "" when the backend agrees with the interpreter, else the failure signature.
  var exp = ""
  try: exp = expected(p)
  except CatchableError: return "INVALID"
  let dir = work / cfg
  let nc = dir / "nc"
  createDir dir
  writeFile(dir / "p.nim", render(p))
  for x in walkDirRec(nc):
    if x.extractFilename == "p": removeFile x
  var flags = ""
  for c in Cfgs:
    if c[0] == cfg: flags = c[1]
  let (o, rc) = execCmdEx(&"timeout 300 {nimony} {flags} --nimcache:{nc} {dir / \"p.nim\"}")
  var exe = ""
  for x in walkDirRec(nc):
    if x.extractFilename == "p" and fpUserExec in getFilePermissions(x): exe = x
  if rc != 0 or exe == "":
    got = o
    return cfg & ":cfail:" & (if rc == 124: "timeout" else: errKey(o))
  let (ro, rrc) = execCmdEx("timeout 20 " & exe)
  got = ro
  if rrc == 124: cfg & ":timeout"
  elif rrc != 0: cfg & ":crash:" & $rrc
  elif ro != exp: cfg & ":mismatch"
  else: ""

# ---- reducer --------------------------------------------------------------------

proc nodes(n: N; res: var seq[N]) =
  res.add n
  for x in n.e: nodes(x, res)
  for x in n.a: nodes(x, res)
  if n.f != nil: nodes(n.f, res)
proc all(p: N): seq[N] = nodes(p, result)

const
  IntK = {eVar, eCall, eAdd, eIfx, eTryx, eBlkx, eLen}
  ListK = {xProg, xProc, xBr, sFor, sBlock, sDefer}

proc reduce(p: N; sig: string): int =
  ## Shrinks `p` in place while `verdict` keeps returning `sig`; returns the tries.
  var tries = 0
  let cfg = sig.split(':')[0]
  proc ok(): bool =
    inc tries
    tries <= budget and verdict(p, cfg) == sig
  var changed = true
  while changed and tries < budget:
    changed = false
    var k = 0
    while k < p.all.len and tries < budget:  # recomputed: an edit detaches nodes
      let n = p.all[k]
      inc k
      if n.k in ListK + {sTry, sCase}:  # delete chunks: procs, statements, arms, of-branches
        let lo = ord(n.k == sTry)
        let hi = ord(n.k == sCase)
        var c = max(1, (n.a.len - lo - hi) div 2)
        while c >= 1:
          var i = lo
          while i < n.a.len - hi:
            let old = n.a
            n.a.delete(i ..< min(i + c, n.a.len - hi))
            if ok(): changed = true
            else:
              n.a = old
              i += c
          c = c div 2
      if n.k in ListK:  # unwrap compound statements, flatten multi-line lets
        var j = 0
        while j < n.a.len:
          let s = n.a[j]
          if s.k in {sIf, sTry, sFor, sBlock, sDefer}:
            let old = n.a
            n.a = n.a[0 ..< j] & (if s.k in {sIf, sTry}: s.a[0].a else: s.a) & n.a[j+1 .. ^1]
            if ok():
              changed = true
              continue
            n.a = old
          elif s.k == sLet and s.a.len > 0:
            let old = s.a
            s.a = @[]
            s.e = @[lit(1)]
            if ok(): changed = true
            else:
              s.a = old
              s.e = @[]
          inc j
      for i in 0 ..< n.e.len:  # an int expression -> 1 or one of its operands
        let x = n.e[i]
        if x.k notin IntK: continue
        for y in @[lit(1)] & x.e.filterIt(it.k in IntK):
          n.e[i] = y
          if ok():
            changed = true
            break
          n.e[i] = x
  tries

# ---- driver ---------------------------------------------------------------------

proc trailer(p: N): string =
  "# EXPECTED\n" & expected(p).splitLines.filterIt(it != "").mapIt("# " & it & "\n").join

proc main() =
  var seed = int(epochTime()) mod 1_000_000
  var count = 10
  var outd = getAppDir() / "out"
  var one = -1
  for kind, key, val in getopt():
    case key
    of "seed": seed = parseInt(val)
    of "count": count = parseInt(val)
    of "nimony": nimony = val
    of "out": outd = val
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
  createDir outd
  let t0 = epochTime()
  var found = 0
  var seen: CountTable[string]
  for k in 0 ..< count:
    let s = seed + k
    let p = make(s)
    var sigs: seq[string]
    var gots: seq[string]
    for c in Cfgs:
      let v = verdict(p, c[0])
      if v != "":
        sigs.add v
        gots.add got
        if c[0] == "c": break  # C already wrong: opt/n would only repeat it
    if sigs.len == 0: echo &"seed {s}: ok"
    for i, sig in sigs:
      inc found
      seen.inc sig
      echo &"seed {s}: {sig}"
      let base = outd / &"{s}_{sig.split(':')[0]}"
      writeFile(base & ".nim", render(p) & trailer(p) & "# ACTUAL\n" & gots[i].splitLines.mapIt("# " & it & "\n").join)
      let log = open(outd / "log.csv", fmAppend)
      log.writeLine &"{epochTime() - t0:.1f},{k + 1},{s},{sig.replace(',', ';')}"
      log.close
      if budget > 0 and seen[sig] <= (if ":cfail:" in sig: 1 else: 3):
        let m = make(s)  # a fresh copy: reduce works in place
        let n = reduce(m, sig)
        discard verdict(m, sig.split(':')[0])
        let src = render(m)
        writeFile(base & ".min.nim", &"# sig: {sig}\n# seed: {s}, {n} reduce tries\n" & src & trailer(m) &
                  "# ACTUAL\n" & got.splitLines.mapIt("# " & it & "\n").join)
        echo &"  reduced to {src.countLines} lines ({n} tries): {base}.min.nim"
  echo &"{count} programs, {found} findings, {int(epochTime() - t0)}s — {outd}"

main()
