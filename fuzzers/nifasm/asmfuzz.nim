## Differential fuzzer: nifasm (x86-64) against GNU `as --64`.
##
## Generates random single instructions (sometimes a short sequence) as raw
## `(lenient)` nifasm procs, writes the same instruction in Intel syntax for
## GNU as, and compares the bytes. Different bytes are disassembled with
## `objdump -M intel` and compared after normalisation, so an alternative
## encoding of the same instruction is not a finding. Verdicts:
##
## * `mismatch`         both accept, the decodes differ;
## * `accepts-invalid`  nifasm accepts what GNU as rejects (or warns about);
## * `rejects-valid`    the reverse (mostly the known "not supported yet" gaps);
## * `hazard`           `div`/`idiv` with a divisor in rdx, which the lowering
##                      zeroes / sign-extends first.
##
## Cases are tiny, so process startup is the cost: a batch of cases is ONE
## nifasm run (a proc per case; a rejected case names its proc, is dropped and
## the rest rerun), ONE `as` run (errors name the line) and ONE objdump run.
## Each case is fenced by `mov r11, MAGIC+i` markers, found by byte search.
##
## The shape pool is mnemonic x operand shapes; a shape nobody accepts (or
## nifasm never accepts) is retired at runtime. Findings are minimized by
## dropping instructions and shrinking operands (regs, index, scale, disp,
## imm), one batch of candidates per step, keeping the same verdict.
##
##   nim c -d:release -o:nifasm/asmfuzz nifasm/asmfuzz.nim
##   nifasm/asmfuzz --seed:1 --minutes:45      # campaign
##   nifasm/asmfuzz --seed:7 --count:2000      # fixed number of cases
##
## `--out:DIR` (default `asmfuzz.out`) gets log.csv (time_s, programs,
## finding_id, kind, signature), findings.txt and summary.txt; `--work:DIR`
## (default `work`) holds the scratch files.

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables, algorithm, sequtils]

type
  Op = object
    k: char          ## 'r' gpr, 'x' xmm, 'i' imm, 'm' mem, 'n' bare trailing int
    w: int           ## bits (r, m; 0 = untyped mem)
    r, ix, sc: int   ## reg or base, index (-1: none), scale
    d: int           ## imm, disp, bare int
    hasD: bool
  Item = (string, seq[Op])
  Case = seq[Item]
  Res = object
    nok, gok: bool
    nb, gb, nerr, gerr, v: string
    nd, gd: seq[string]

const
  R64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split
  R32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split
  R16 = "ax cx dx bx sp bp si di r8w r9w r10w r11w r12w r13w r14w r15w".split
  R8 = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split
  Imms = [0, 1, -1, 2, 127, 128, -128, -129, 255, 256, 32767, 32768, -32768, -32769,
    65535, 65536, 0x7fffffff, 0x80000000, -0x80000000, -0x80000001, 0xffffffff,
    0x100000000, high(int), low(int), 63, 64, 31, 32, 7, 8]  # no >= 2^63: crashes nifasm (08.md)
  Disps = [0, 1, 127, -128, 128, -129, 255, 4096, -4096, 0x7fffffff, -0x80000000, 1000, -300]
  Cond = "e z ne nz a nbe ae nb nc b nae c be na g nle ge nl l nge le ng o no s ns p np pe po".split
  SetCond = "e z ne nz a nbe ae nb nc b nae c be na g nle ge nl l nge le ng o s p".split
  Alpha = "r8 r16 r32 r64 m8 m16 m32 m64 mraw i x cl".split
  M1 = "inc dec neg not push pop mul div idiv setcc bswap clflush prefetcht0 cmpxchg8b lea".split
  M2 = ("add sub and or xor cmp test adc sbb mov shl shr sal sar rol ror rcl rcr bt bts btr btc " &
    "xchg cmpxchg xadd bsf bsr imul lea cmovcc addsd subsd mulsd divsd movsd sqrtsd comisd " &
    "addss subss mulss divss movss sqrtss comiss movapd movdqu movupd movups addpd subpd mulpd " &
    "addps subps mulps punpcklqdq movfq movfd cvtsi2sd cvtsi2ss cvttsd2si cvttss2si cvtsd2ss cvtss2sd").split
  Zero = "ret nop syscall mfence sfence lfence pause repmovsb repmovsw repmovsd repmovsq repstosb repstosq".split
  Lockable = "add sub and or xor adc sbb xadd cmpxchg xchg btc bts btr inc dec neg not".split
  Magic = 0x5AC1635200000000
  Batch = 64

var
  nifasm = "/home/ageralis/Projects/nimony/bin/nifasm"
  work = "work"
  rng: Rand

proc rn(w: int): seq[string] = (if w == 8: R8 elif w == 16: R16 elif w == 32: R32 else: R64)
proc ptrOf(w: int): string = (if w == 8: "byte ptr " elif w == 16: "word ptr " elif w == 32: "dword ptr " elif w == 64: "qword ptr " else: "")

# ---- operands and rendering --------------------------------------------------------

proc build(o: Op): (string, string) =
  case o.k
  of 'r': ((if o.w == 64: "(" & R64[o.r] & ")" else: &"(cast (u {o.w}) ({R64[o.r]}))"), rn(o.w)[o.r])
  of 'x': (&"(xmm{o.r})", &"xmm{o.r}")
  of 'i', 'n': ($o.d, $o.d)
  else:
    var n = "(mem (" & R64[o.r] & ")"
    var g = R64[o.r]
    if o.ix >= 0:
      n.add &" ({R64[o.ix]}) {o.sc}"
      g.add &"+{R64[o.ix]}*{o.sc}"
    if o.hasD:
      n.add " " & $o.d
      g.add (if o.d >= 0: "+" else: "") & $o.d
    n.add ")"
    ((if o.w > 0: &"(cast (u {o.w}) {n})" else: n), ptrOf(o.w) & "[" & g & "]")

proc render(it: Item): (string, string) =
  var (mn, ops) = it
  if mn.startsWith("lock "):
    let (n, g) = render((mn[5..^1], ops))
    return ("(lock " & n & ")", "lock " & g)
  var ns, gs: seq[string]
  var num = -1
  for o in ops:
    let (n, g) = build(o)
    ns.add n
    if o.k == 'n': num = o.d else: gs.add g
  var nif = "(" & mn & (if ns.len > 0: " " & ns.join(" ") else: "") & ")"
  var gm = mn
  case mn
  of "movfq": gm = "movq"
  of "movfd":
    gm = "movd"
    for i, o in ops:
      if o.k == 'r' and o.w == 64: gs[i] = R32[o.r]
  of "div", "idiv":
    if ops.len == 1:
      return (&"({mn} (rdx) (rax) {ns[0]})", (if mn == "div": "xor rdx, rdx\n" else: "cqo\n") & mn & " " & gs[0])
  of "movzx":
    if num == 32:
      gm = "mov"
      gs[0] = R32[ops[0].r]
  of "movsx":
    if num == 32: gm = "movsxd"
  of "bswap":
    if num > 0: gs[0] = rn(num)[ops[0].r]
  of "imul3":
    nif = "(imul " & ns.join(" ") & ")"
    gm = "imul"
  else:
    if mn.startsWith("rep"): gm = "rep " & mn[3..^1]
  (nif, gm & (if gs.len > 0: " " & gs.join(", ") else: ""))

proc hazard(c: Case): bool =
  for (mn, ops) in c:
    if mn in ["div", "idiv"] and ops.len == 1:
      let o = ops[0]
      if o.r == 2 and o.k in {'r', 'm'} or o.k == 'm' and o.ix == 2: return true

proc randOp(s: string): Op =
  case s[0]
  of 'c': Op(k: 'r', w: 8, r: 1)
  of 'r': Op(k: 'r', w: parseInt(s[1..^1]), r: rng.rand(15))
  of 'x': Op(k: 'x', r: rng.rand(15))
  of 'n': Op(k: 'n', d: parseInt(s[1..^1]))
  of 'i': Op(k: 'i', d: (if rng.rand(1.0) < 0.85: rng.sample(Imms) else: rng.rand(-1 shl 31 .. 1 shl 31)))
  else:
    var ix = rng.rand(14)
    if ix >= 4: inc ix
    Op(k: 'm', w: (if s == "mraw": 0 else: parseInt(s[1..^1])), r: rng.rand(15),
       ix: (if rng.rand(1.0) < 0.5: ix else: -1), sc: rng.sample([1, 2, 4, 8]),
       hasD: rng.rand(13) > 0, d: rng.sample(Disps))

proc item(key: seq[string]): Item =
  var mn = key[0]
  if mn == "setcc": mn = "set" & rng.sample(SetCond)
  elif mn == "cmovcc": mn = "cmov" & rng.sample(Cond)
  var ops: seq[Op]
  for s in key[1..^1]: ops.add randOp(s)
  if mn in Lockable and ops.len > 0 and ops[0].k == 'm' and rng.rand(1.0) < 0.15: mn = "lock " & mn
  (mn, ops)

proc pool(): seq[seq[string]] =
  for m in M1:
    for a in Alpha: result.add @[m, a]
  for m in M2:
    for a in Alpha:
      for b in Alpha: result.add @[m, a, b]
  for m in Zero: result.add @[m]
  for m in ["movzx", "movsx"]:
    for n in ["n8", "n16", "n32"]:
      for s in "r8 r16 r32 r64 m8 m16 m32 m64".split: result.add @[m, "r64", s, n]
  for n in ["n16", "n32", "n64"]:
    for s in "r16 r32 r64 m16 m32 m64".split:
      result.add @["popcnt", "r64", s, n]
      result.add @["popcnt", "r32", s, n]
    for s in ["r16", "r32", "r64"]: result.add @["bswap", s, n]
  for d in ["r16", "r32", "r64"]:
    for s in "r16 r32 r64 m16 m32 m64 mraw".split: result.add @["imul3", d, s, "i"]

# ---- running the tools (one process per batch) --------------------------------------

proc markers(b: string): Table[int, string] =
  ## case index -> bytes between its `mov r11, Magic+2i` and `Magic+2i+1` markers
  var start: Table[int, int]
  var p = 0
  while true:
    p = b.find("\x49\xbb", p)
    if p < 0 or p + 10 > b.len: break
    var v = 0
    for j in countdown(9, 2): v = v shl 8 or ord(b[p + j])
    if v shr 32 == Magic shr 32:
      let i = (v and 0xffffffff) shr 1
      if (v and 1) == 0: start[i] = p + 10
      elif i in start: result[i] = b[start[i] ..< p]
      p += 10
    else: inc p

proc nifRun(cs: seq[Case]; idx: seq[int]; rs: var seq[Res]) =
  var idx = idx
  let src = work / "b.nif"
  let outf = work / "b.out"
  while idx.len > 0:
    var s = "(.nif27)\n(.index)\n(stmts\n"
    for i in idx:
      var body = ""
      for it in cs[i]: body.add " " & render(it)[0]
      s.add &"(proc :c{i}.0 (params) (result) (clobber) (lenient) (stmts (mov (r11) {Magic + 2*i}){body} (mov (r11) {Magic + 2*i + 1})))\n"
    writeFile(src, s & ")\n")
    removeFile(outf)
    let (o, code) = execCmdEx(quoteShell(nifasm) & " -o:" & quoteShell(outf) & " " & quoteShell(src))
    if code == 0 and fileExists(outf):
      let m = markers(readFile(outf))
      for i in idx:
        rs[i].nok = true
        rs[i].nb = m.getOrDefault(i)
      return
    let k = o.find("in proc c")
    var bad = -1
    if k >= 0:
      var j = k + 9
      while j < o.len and o[j].isDigit: inc j
      if j > k + 9: bad = parseInt(o[k + 9 ..< j])
    if bad in idx:
      rs[bad].nerr = o.strip
      idx.delete(idx.find(bad))
    elif idx.len == 1:
      rs[idx[0]].nerr = o.strip
      return
    else:                 # unattributed (a crash): bisect
      nifRun(cs, idx[0 ..< idx.len div 2], rs)
      nifRun(cs, idx[idx.len div 2 .. ^1], rs)
      return

proc gasRun(cs: seq[Case]; rs: var seq[Res]) =
  var idx = toSeq(0 ..< cs.len)
  let src = work / "b.s"
  let outf = work / "b.o"
  while idx.len > 0:
    var s = ".intel_syntax noprefix\n.text\n"
    var owner = @[-1, -1, -1]   # line number (1-based) -> case
    for i in idx:
      var lines = @[&"mov r11, {Magic + 2*i}"]
      for it in cs[i]: lines.add render(it)[1].splitLines
      lines.add &"mov r11, {Magic + 2*i + 1}"
      for l in lines:
        s.add l & "\n"
        owner.add i
    writeFile(src, s)
    removeFile(outf)
    let (o, code) = execCmdEx("as --64 -o " & quoteShell(outf) & " " & quoteShell(src))
    var bad: seq[int]
    for l in o.splitLines:
      let p = l.split(':', 3)
      if p.len == 4 and p[1].strip.allCharsInSet(Digits) and p[1].len > 0:
        let i = owner[parseInt(p[1])]
        if i < 0: continue
        rs[i].gerr.add l.strip & "\n"
        if i notin bad: bad.add i
    if code == 0 and fileExists(outf):
      let m = markers(readFile(outf))
      for i in idx:
        if i notin bad:
          rs[i].gok = true
          rs[i].gb = m.getOrDefault(i)
      return
    if bad.len == 0:
      for i in idx: rs[i].gerr = o
      return
    idx.keepItIf(it notin bad)

proc norm(l: string): string =
  l.splitWhitespace.join(" ").replace("+0x0]", "]").replace("data16 ", "")

proc disasm(bs: seq[string]): seq[seq[string]] =
  ## one objdump call for all byte strings
  result = newSeq[seq[string]](bs.len)
  var files: seq[string]
  var which: Table[string, int]
  for i, b in bs:
    if b.len == 0: continue
    let f = work / &"d{i}.bin"
    writeFile(f, b)
    files.add quoteShell(f)
    which[f] = i
  if files.len == 0: return
  let (o, _) = execCmdEx("objdump -D -b binary -mi386:x86-64 -M intel " & files.join(" "))
  var cur = -1
  for l in o.splitLines:
    if l.endsWith("file format binary"): cur = which.getOrDefault(l.split(":")[0], -1)
    else:
      let p = l.split('\t')
      if cur >= 0 and p.len >= 3 and p[0].strip.endsWith(":"): result[cur].add norm(p[2 .. ^1].join(" "))

proc isNop(s: string): bool =
  if s == "nop": return true
  let p = s.split(' ', 1)
  if p[0] != "lea" or p.len < 2: return false
  let q = p[1].split(',')
  q.len == 2 and q[1] == "[" & q[0] & "]"

proc eval(cs: seq[Case]): seq[Res] =
  result = newSeq[Res](cs.len)
  nifRun(cs, toSeq(0 ..< cs.len), result)
  gasRun(cs, result)
  var need: seq[int]
  for i, r in result.mpairs:
    r.v = if not r.nok and not r.gok: "ok"
          elif not r.nok: "rejects-valid"
          elif not r.gok: "accepts-invalid"
          elif r.nb == r.gb: "ok"
          elif r.nb.len == 3 and r.nb[0] == '\x48' and r.nb[1] == '\x87' and (ord(r.nb[2]) shr 6) == 3 and
               ((ord(r.nb[2]) shr 3) and 7) == (ord(r.nb[2]) and 7) and r.gb == "\x90": "ok"   # xchg r,r == nop
          else: (need.add i; "?")
    if r.v == "ok" and hazard(cs[i]): r.v = "hazard"
  if need.len == 0: return
  var bs: seq[string]
  for i in need: bs.add [result[i].nb, result[i].gb]
  let ds = disasm(bs)
  for j, i in need:
    let r = addr result[i]
    r.nd = ds[2*j]
    r.gd = ds[2*j + 1]
    r.v = if r.nb.len == 0 and r.gd.len > 0 and isNop(r.gd[0]): "ok"
          elif r.nd == r.gd: "ok"
          else: "mismatch"

proc errKey(e: string): string =
  for l in e.splitLines:
    if "Error" in l:
      result = l.strip
      for cut in [" at ???", " in proc"]:
        let k = result.find(cut)
        if k >= 0: result = result[0 ..< k]
      return result[0 ..< min(result.len, 90)]
  let l = e.strip.splitLines[^1]
  l[0 ..< min(l.len, 90)]

proc key(r: Res): string =
  if r.v == "rejects-valid": r.v & " :: " & errKey(r.nerr) else: r.v

# ---- minimizer ---------------------------------------------------------------------

proc shrinks(o: Op): seq[Op] =
  template alt(f, v) =
    var y = o
    y.f = v
    when astToStr(f) == "ix": (if v < 0: y.sc = 1)
    result.add y
  case o.k
  of 'r', 'x':
    for i in 0..1:
      if o.r > i and (o.k == 'r' or i == 0): alt(r, i)
  of 'i':
    for v in [0, 1, 5]:
      if o.d == low(int) or abs(v) < abs(o.d): alt(d, v)
  of 'm':
    if o.ix >= 0: alt(ix, -1)
    if o.ix >= 0 and o.sc != 1: alt(sc, 1)
    if o.hasD: alt(hasD, false)
    if o.hasD and o.d notin [0, 1]: alt(d, 1)
    if o.ix > 1: alt(ix, 1)
    for b in 0..1:
      if o.r > b: alt(r, b)
  else: discard

proc minimize(c: Case; k: string): Case =
  result = c
  while true:
    var cands: seq[Case]
    if result.len > 1:
      for i in 0 ..< result.len:
        var t = result
        t.delete(i)
        cands.add t
    for i, (mn, ops) in result:
      for j, o in ops:
        for s in shrinks(o):
          var t = result
          t[i][1][j] = s
          cands.add t
    if cands.len == 0: return
    var hit = -1
    for start in countup(0, cands.len - 1, Batch):
      let rs = eval(cands[start ..< min(cands.len, start + Batch)])
      for j, r in rs:
        if key(r) == k:
          hit = start + j
          break
      if hit >= 0: break
    if hit < 0: return
    result = cands[hit]

# ---- driver ------------------------------------------------------------------------

proc hex(b: string): string =
  for c in b: result.add toHex(ord(c), 2).toLowerAscii & " "

proc main() =
  var seed = 1
  var count = 0
  var minutes = 0.0
  var outDir = "asmfuzz.out"
  for kind, k, v in getopt():
    case k
    of "seed": seed = parseInt(v)
    of "count": count = parseInt(v)
    of "minutes": minutes = parseFloat(v)
    of "out": outDir = v
    of "work": work = v
    of "nifasm": nifasm = v
    else: quit "unknown option: " & k
  if count == 0 and minutes == 0: count = 1000
  rng = initRand(seed)
  createDir(outDir)
  createDir(work)
  let keys = pool()
  var tries, nAcc, anyAcc = newSeq[int](keys.len)
  var live = toSeq(0 ..< keys.len)
  let logf = open(outDir / "log.csv", fmAppend)
  let fnd = open(outDir / "findings.txt", fmAppend)
  if logf.getFileSize == 0: logf.writeLine "time_s,programs,finding_id,kind,signature"
  var seen: Table[string, int]
  var capped: CountTable[string]
  var counts: CountTable[string]
  var n, fid = 0
  let t0 = epochTime()
  while (if count > 0: n < count else: epochTime() - t0 < minutes * 60):
    var cs: seq[Case]
    var ks: seq[int]
    for b in 0 ..< (if count > 0: min(Batch, count - n) else: Batch):
      let k = rng.sample(live)
      var c = @[item(keys[k])]
      if rng.rand(1.0) < 0.1:
        for j in 0 .. rng.rand(2): c.insert(item(keys[rng.sample(live)]), 0)
      cs.add c
      ks.add (if c.len == 1 and not c[0][0].startsWith("lock "): k else: -1)
    let rs = eval(cs)
    for i, r in rs:
      inc n
      counts.inc r.v
      if ks[i] >= 0:
        inc tries[ks[i]]
        if r.nok: inc nAcc[ks[i]]
        if r.nok or r.gok: inc anyAcc[ks[i]]
      if r.v == "ok": continue
      let pre = r.v & " " & cs[i].mapIt(it[0]).join(",") & " " & (if ks[i] >= 0: keys[ks[i]].join(",") else: "seq")
      capped.inc pre
      if capped[pre] > 6: continue
      let m = if r.v == "hazard": cs[i].filterIt(hazard(@[it]))[0 .. 0] else: minimize(cs[i], key(r))
      var r2 = eval(@[m])[0]
      let ds = disasm(@[r2.nb, r2.gb])
      (r2.nd, r2.gd) = (ds[0], ds[1])
      var nif, gas: seq[string]
      for it in m:
        let (a, b) = render(it)
        nif.add a
        gas.add b
      var sig = r.v & " | " & nif.join(" ")
      if r.v == "rejects-valid": sig.add " :: " & errKey(r2.nerr)
      if sig in seen:
        inc seen[sig]
        continue
      seen[sig] = 1
      inc fid
      let el = int(epochTime() - t0)
      logf.writeLine &"{el},{n},{fid},{r.v},\"" & sig.replace('"', '\'') & "\""
      logf.flushFile
      fnd.write &"## {fid} {r.v} t={el}s n={n}\nnif: {nif.join(\" \")}\ngas: {gas.join(\"; \")}\n" &
        (if r2.nok: &"nifasm: {hex(r2.nb)}| {r2.nd.join(\"; \")}\n" else: &"nifasm rejects: {errKey(r2.nerr)}\n") &
        (if r2.gok: &"as:     {hex(r2.gb)}| {r2.gd.join(\"; \")}\n\n" else: &"as rejects: {r2.gerr.strip}\n\n")
      fnd.flushFile
      echo &"{el}s #{n} {sig}"
    # retire shapes nobody accepts, and shapes nifasm never accepts (known gaps)
    live.keepItIf(not (tries[it] >= 2 and anyAcc[it] == 0 or tries[it] >= 8 and nAcc[it] == 0))
    if live.len == 0: break
  let wall = epochTime() - t0
  var cnt: seq[string]
  for k, v in counts: cnt.add &"{k}={v}"
  cnt.sort
  let s = &"seed={seed} programs={n} wall_s={int(wall)} cases_per_s={n.float / wall:.1f} cpu_s={cpuTime():.1f} " &
          &"distinct_sigs={seen.len} live_shapes={live.len}/{keys.len} {cnt.join(\" \")}"
  let f = open(outDir / "summary.txt", fmAppend)
  f.writeLine s
  f.close
  echo s

main()
