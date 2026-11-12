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
## (default `work`) holds the scratch files; `--nifasm:PATH` picks the binary.

import std / [os, osproc, strutils, random, times, strformat, parseopt, tables, algorithm]

type
  Operand = object
    kind: char         ## 'r' gpr, 'x' xmm, 'i' imm, 'm' mem, 'n' bare trailing int
    bits: int          ## width for 'r' and 'm' (0 = untyped mem)
    reg: int           ## register, or the base of a mem operand
    index, scale: int  ## mem index register (-1: none) and its scale
    val: int           ## imm, disp or bare int
    hasDisp: bool
  Instr = (string, seq[Operand])  ## mnemonic, operands
  Case = seq[Instr]
  Outcome = object
    nifOk, gasOk: bool           ## the assembler accepted the case
    nifBytes, gasBytes: string   ## encoding between the markers
    nifErr, gasErr: string
    verdict: string              ## "ok", "mismatch", ... (see module doc)
    nifAsm, gasAsm: seq[string]  ## normalised objdump lines, only when the bytes differ

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
  Slots = "r8 r16 r32 r64 m8 m16 m32 m64 mraw i x cl".split  ## operand shapes, see `randOp`
  Unary = "inc dec neg not push pop mul div idiv setcc bswap clflush prefetcht0 cmpxchg8b lea".split
  Binary = ("add sub and or xor cmp test adc sbb mov shl shr sal sar rol ror rcl rcr bt bts btr btc " &
    "xchg cmpxchg xadd bsf bsr imul lea cmovcc addsd subsd mulsd divsd movsd sqrtsd comisd " &
    "addss subss mulss divss movss sqrtss comiss movapd movdqu movupd movups addpd subpd mulpd " &
    "addps subps mulps punpcklqdq movfq movfd cvtsi2sd cvtsi2ss cvttsd2si cvttss2si cvtsd2ss cvtss2sd").split
  Nullary = "ret nop syscall mfence sfence lfence pause repmovsb repmovsw repmovsd repmovsq repstosb repstosq".split
  Lockable = "add sub and or xor adc sbb xadd cmpxchg xchg btc bts btr inc dec neg not".split
  Magic = 0x5AC1635200000000  ## high half tags a marker; low half is 2*case (+1 at the end)
  Batch = 64

var
  nifasm = "/home/ageralis/Projects/nimony/bin/nifasm"
  work = "work"
  rng: Rand

proc regs(bits: int): seq[string] = (if bits == 8: R8 elif bits == 16: R16 elif bits == 32: R32 else: R64)
proc ptrOf(bits: int): string = (if bits == 8: "byte ptr " elif bits == 16: "word ptr " elif bits == 32: "dword ptr " elif bits == 64: "qword ptr " else: "")

# ---- operands and rendering --------------------------------------------------------

proc renderOp(o: Operand): (string, string) =
  ## (nifasm, GNU as) text of one operand
  case o.kind
  of 'r': ((if o.bits == 64: "(" & R64[o.reg] & ")" else: &"(cast (u {o.bits}) ({R64[o.reg]}))"), regs(o.bits)[o.reg])
  of 'x': (&"(xmm{o.reg})", &"xmm{o.reg}")
  of 'i', 'n': ($o.val, $o.val)
  else:
    var n = "(mem (" & R64[o.reg] & ")"
    var g = R64[o.reg]
    if o.index >= 0:
      n.add &" ({R64[o.index]}) {o.scale}"
      g.add &"+{R64[o.index]}*{o.scale}"
    if o.hasDisp:
      n.add " " & $o.val
      g.add (if o.val >= 0: "+" else: "") & $o.val
    n.add ")"
    ((if o.bits > 0: &"(cast (u {o.bits}) {n})" else: n), ptrOf(o.bits) & "[" & g & "]")

proc render(it: Instr): (string, string) =
  ## (nifasm, GNU as) text of one instruction; translates pseudo-mnemonics
  ## (`movfq`, `imul3`, `repmovsb`...). The as side may span several lines.
  var (mn, ops) = it
  if mn.startsWith("lock "):
    let (n, g) = render((mn[5..^1], ops))
    return ("(lock " & n & ")", "lock " & g)
  var ns, gs: seq[string]
  var num = -1   # bare trailing int (a width); as has no operand for it
  for o in ops:
    let (n, g) = renderOp(o)
    ns.add n
    if o.kind == 'n': num = o.val else: gs.add g
  var nif = "(" & mn & (if ns.len > 0: " " & ns.join(" ") else: "") & ")"
  var gm = mn
  case mn
  of "movfq": gm = "movq"
  of "movfd":
    gm = "movd"
    for i, o in ops:
      if o.kind == 'r' and o.bits == 64: gs[i] = R32[o.reg]
  of "div", "idiv":
    # nifasm's div names rdx:rax and sets up rdx itself; as needs that spelled out
    if ops.len == 1:
      return (&"({mn} (rdx) (rax) {ns[0]})", (if mn == "div": "xor rdx, rdx\n" else: "cqo\n") & mn & " " & gs[0])
  of "movzx":
    if num == 32:   # a 32-bit mov zero-extends already
      gm = "mov"
      gs[0] = R32[ops[0].reg]
  of "movsx":
    if num == 32: gm = "movsxd"
  of "bswap":
    if num > 0: gs[0] = regs(num)[ops[0].reg]
  of "imul3":
    nif = "(imul " & ns.join(" ") & ")"
    gm = "imul"
  else:
    if mn.startsWith("rep"): gm = "rep " & mn[3..^1]
  (nif, gm & (if gs.len > 0: " " & gs.join(", ") else: ""))

proc hazard(c: Case): bool =
  ## `div`/`idiv` whose divisor uses rdx, which the lowering clobbers first
  for (mn, ops) in c:
    if mn in ["div", "idiv"] and ops.len == 1:
      let o = ops[0]
      if o.reg == 2 and o.kind in {'r', 'm'} or o.kind == 'm' and o.index == 2: return true

proc randOp(slot: string): Operand =
  case slot[0]
  of 'c': Operand(kind: 'r', bits: 8, reg: 1)
  of 'r': Operand(kind: 'r', bits: parseInt(slot[1..^1]), reg: rng.rand(15))
  of 'x': Operand(kind: 'x', reg: rng.rand(15))
  of 'n': Operand(kind: 'n', val: parseInt(slot[1..^1]))
  of 'i': Operand(kind: 'i', val: (if rng.rand(1.0) < 0.85: rng.sample(Imms) else: rng.rand(-1 shl 31 .. 1 shl 31)))
  else:
    var ix = rng.rand(14)
    if ix >= 4: inc ix   # rsp cannot be an index
    Operand(kind: 'm', bits: (if slot == "mraw": 0 else: parseInt(slot[1..^1])), reg: rng.rand(15),
       index: (if rng.rand(1.0) < 0.5: ix else: -1), scale: rng.sample([1, 2, 4, 8]),
       hasDisp: rng.rand(13) > 0, val: rng.sample(Disps))

proc instr(shape: seq[string]): Instr =
  ## a random instruction of `shape` (mnemonic, then operand slots)
  var mn = shape[0]
  if mn == "setcc": mn = "set" & rng.sample(SetCond)
  elif mn == "cmovcc": mn = "cmov" & rng.sample(Cond)
  var ops: seq[Operand]
  for s in shape[1..^1]: ops.add randOp(s)
  if mn in Lockable and ops.len > 0 and ops[0].kind == 'm' and rng.rand(1.0) < 0.15: mn = "lock " & mn
  (mn, ops)

proc shapePool(): seq[seq[string]] =
  for m in Unary:
    for a in Slots: result.add @[m, a]
  for m in Binary:
    for a in Slots:
      for b in Slots: result.add @[m, a, b]
  for m in Nullary: result.add @[m]
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
    p = b.find("\x49\xbb", p)   # REX.W `mov r11, imm64`
    if p < 0 or p + 10 > b.len: break
    var v = 0
    for j in countdown(9, 2): v = v shl 8 or ord(b[p + j])
    if v shr 32 == Magic shr 32:
      let i = (v and 0xffffffff) shr 1
      if (v and 1) == 0: start[i] = p + 10
      elif i in start: result[i] = b[start[i] ..< p]
      p += 10
    else: inc p

proc runNifasm(cs: seq[Case]; idx: seq[int]; rs: var seq[Outcome]) =
  ## assembles cases `idx` in one file, one proc `c<i>` each
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
        rs[i].nifOk = true
        rs[i].nifBytes = m.getOrDefault(i)
      return
    # nifasm stops at the first error, which names the proc: drop that case, rerun the rest
    let k = o.find("in proc c")
    var bad = -1
    if k >= 0:
      var j = k + 9
      while j < o.len and o[j].isDigit: inc j
      if j > k + 9: bad = parseInt(o[k + 9 ..< j])
    if bad in idx:
      rs[bad].nifErr = o.strip
      idx.delete(idx.find(bad))
    elif idx.len == 1:
      rs[idx[0]].nifErr = o.strip
      return
    else:                 # unattributed (a crash): bisect
      runNifasm(cs, idx[0 ..< idx.len div 2], rs)
      runNifasm(cs, idx[idx.len div 2 .. ^1], rs)
      return

proc runGas(cs: seq[Case]; idx: seq[int]; rs: var seq[Outcome]) =
  ## assembles cases `idx` in one file
  var idx = idx
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
    # as reports every bad line (warnings too): all those cases are rejects, the rest rerun
    var bad: seq[int]
    for l in o.splitLines:
      # `file:line: message`
      let a = l.find(':')
      let b = if a < 0: -1 else: l.find(':', a + 1)
      if b < 0 or l.find(':', b + 1) < 0: continue
      let num = l.substr(a + 1, b - 1)
      if num.len > 0 and num.allCharsInSet(Digits):
        let i = owner[parseInt(num)]
        if i < 0: continue
        rs[i].gasErr.add l.strip & "\n"
        if i notin bad: bad.add i
    if code == 0 and fileExists(outf):
      let m = markers(readFile(outf))
      for i in idx:
        if i notin bad:
          rs[i].gasOk = true
          rs[i].gasBytes = m.getOrDefault(i)
      return
    if bad.len == 0:
      for i in idx: rs[i].gasErr = o
      return
    var rest: seq[int]
    for i in idx:
      if i notin bad: rest.add i
    idx = rest

proc normalize(l: string): string =
  ## hides objdump spellings that differ between equivalent encodings (zero disp, 0x66 prefix)
  for w in l.splitWhitespace:
    if result.len > 0: result.add ' '
    result.add w
  result = result.replace("+0x0]", "]").replace("data16 ", "")

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
    if l.endsWith("file format binary"): cur = which.getOrDefault(l.substr(0, l.find(':') - 1), -1)
    elif cur >= 0:
      # `   addr:\tbytes\tinstruction`
      let t1 = l.find('\t')
      let t2 = if t1 < 0: -1 else: l.find('\t', t1 + 1)
      if t2 < 0: continue
      var e = t1 - 1
      while e >= 0 and l[e] in Whitespace: dec e
      if e >= 0 and l[e] == ':': result[cur].add normalize(l.substr(t2 + 1))

proc isNop(s: string): bool =
  ## `nop` or `lea r, [r]`, where nifasm may emit nothing
  if s == "nop": return true
  if not s.startsWith("lea "): return false
  let c = s.find(',')
  c >= 0 and s.find(',', c + 1) < 0 and s.substr(c + 1) == "[" & s.substr(4, c - 1) & "]"

proc eval(cs: seq[Case]): seq[Outcome] =
  ## runs both assemblers on the batch, objdump only where the bytes differ
  result = newSeq[Outcome](cs.len)
  var all: seq[int]
  for i in 0 ..< cs.len: all.add i
  runNifasm(cs, all, result)
  runGas(cs, all, result)
  var unsure: seq[int]
  for i, r in result.mpairs:
    r.verdict = if not r.nifOk and not r.gasOk: "ok"
                elif not r.nifOk: "rejects-valid"
                elif not r.gasOk: "accepts-invalid"
                elif r.nifBytes == r.gasBytes: "ok"
                elif r.nifBytes.len == 3 and r.nifBytes[0] == '\x48' and r.nifBytes[1] == '\x87' and (ord(r.nifBytes[2]) shr 6) == 3 and
                     ((ord(r.nifBytes[2]) shr 3) and 7) == (ord(r.nifBytes[2]) and 7) and r.gasBytes == "\x90": "ok"   # xchg r,r == nop
                else: (unsure.add i; "?")
    if r.verdict == "ok" and hazard(cs[i]): r.verdict = "hazard"
  if unsure.len == 0: return
  var bs: seq[string]
  for i in unsure: bs.add [result[i].nifBytes, result[i].gasBytes]
  let ds = disasm(bs)
  for j, i in unsure:
    let r = addr result[i]
    r.nifAsm = ds[2*j]
    r.gasAsm = ds[2*j + 1]
    r.verdict = if r.nifBytes.len == 0 and r.gasAsm.len > 0 and isNop(r.gasAsm[0]): "ok"
                elif r.nifAsm == r.gasAsm: "ok"
                else: "mismatch"

proc errKey(e: string): string =
  ## the error message without its location, so equal errors group together
  for l in e.splitLines:
    if "Error" in l:
      result = l.strip
      for cut in [" at ???", " in proc"]:
        let k = result.find(cut)
        if k >= 0: result.setLen k
      return result.substr(0, 89)
  let s = e.strip
  let k = s.rfind({'\r', '\n'})   # the last line
  s.substr(k + 1, k + 90)

proc bucket(r: Outcome): string =
  ## what the minimizer must keep: the verdict, plus the error for rejects
  if r.verdict == "rejects-valid": r.verdict & " :: " & errKey(r.nifErr) else: r.verdict

# ---- minimizer ---------------------------------------------------------------------

proc shrinks(o: Operand): seq[Operand] =
  ## simpler variants of `o`, one change each
  template alt(f, v) =
    var y = o
    y.f = v
    result.add y
  case o.kind
  of 'r', 'x':
    for i in 0..1:
      if o.reg > i and (o.kind == 'r' or i == 0): alt(reg, i)
  of 'i':
    for v in [0, 1, 5]:
      if o.val == low(int) or abs(v) < abs(o.val): alt(val, v)
  of 'm':
    if o.index >= 0:   # no index: scale back to 1
      var y = o
      (y.index, y.scale) = (-1, 1)
      result.add y
    if o.index >= 0 and o.scale != 1: alt(scale, 1)
    if o.hasDisp: alt(hasDisp, false)
    if o.hasDisp and o.val notin [0, 1]: alt(val, 1)
    if o.index > 1: alt(index, 1)
    for b in 0..1:
      if o.reg > b: alt(reg, b)
  else: discard

proc minimize(c: Case; want: string): Case =
  ## greedy: take the first candidate that keeps bucket `want`, until none does
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
        if bucket(r) == want:
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
  let shapes = shapePool()
  var tries, nifAcc, anyAcc = newSeq[int](shapes.len)   # per shape, plain single-instruction cases only
  var live: seq[int]
  for k in 0 ..< shapes.len: live.add k
  let log = open(outDir / "log.csv", fmAppend)
  let findings = open(outDir / "findings.txt", fmAppend)
  if log.getFileSize == 0: log.writeLine "time_s,programs,finding_id,kind,signature"
  var seen: seq[string]   # signatures already reported
  var capped: CountTable[string]   # findings per group before minimizing; caps the expensive repeats
  var counts: CountTable[string]
  var total, fid = 0
  let start = epochTime()
  while (count == 0 or total < count) and (minutes == 0 or epochTime() - start < minutes * 60):
    var batch: seq[Case]
    var shapeOf: seq[int]   # -1: a sequence or locked, so it says nothing about one shape
    for b in 0 ..< (if count > 0: min(Batch, count - total) else: Batch):
      let k = rng.sample(live)
      var c = @[instr(shapes[k])]
      if rng.rand(1.0) < 0.1:
        for j in 0 .. rng.rand(2): c.insert(instr(shapes[rng.sample(live)]), 0)
      batch.add c
      shapeOf.add (if c.len == 1 and not c[0][0].startsWith("lock "): k else: -1)
    let rs = eval(batch)
    for i, r in rs:
      inc total
      counts.inc r.verdict
      if shapeOf[i] >= 0:
        inc tries[shapeOf[i]]
        if r.nifOk: inc nifAcc[shapeOf[i]]
        if r.nifOk or r.gasOk: inc anyAcc[shapeOf[i]]
      if r.verdict == "ok": continue
      var mns: seq[string]
      for it in batch[i]: mns.add it[0]
      let group = r.verdict & " " & mns.join(",") & " " & (if shapeOf[i] >= 0: shapes[shapeOf[i]].join(",") else: "seq")
      capped.inc group
      if capped[group] > 6: continue
      # a hazard is one instruction's property: keep that instruction, no minimizing
      var small: Case
      if r.verdict == "hazard":
        for it in batch[i]:
          if hazard(@[it]):
            small = @[it]
            break
      else: small = minimize(batch[i], bucket(r))
      var again = eval(@[small])[0]
      let ds = disasm(@[again.nifBytes, again.gasBytes])
      (again.nifAsm, again.gasAsm) = (ds[0], ds[1])
      var nif, gas: seq[string]
      for it in small:
        let (a, b) = render(it)
        nif.add a
        gas.add b
      var sig = r.verdict & " | " & nif.join(" ")
      if r.verdict == "rejects-valid": sig.add " :: " & errKey(again.nifErr)
      if sig in seen: continue
      seen.add sig
      inc fid
      let secs = int(epochTime() - start)
      log.writeLine &"{secs},{total},{fid},{r.verdict},\"" & sig.replace('"', '\'') & "\""
      log.flushFile
      findings.write &"## {fid} {r.verdict} t={secs}s n={total}\nnif: {nif.join(\" \")}\ngas: {gas.join(\"; \")}\n" &
        (if again.nifOk: &"nifasm: {hex(again.nifBytes)}| {again.nifAsm.join(\"; \")}\n" else: &"nifasm rejects: {errKey(again.nifErr)}\n") &
        (if again.gasOk: &"as:     {hex(again.gasBytes)}| {again.gasAsm.join(\"; \")}\n\n" else: &"as rejects: {again.gasErr.strip}\n\n")
      findings.flushFile
      echo &"{secs}s #{total} {sig}"
    # retire shapes nobody accepts and shapes nifasm never accepts (known gaps):
    # they only repeat `ok` or the same rejects-valid and waste the budget
    var keep: seq[int]
    for k in live:
      if not (tries[k] >= 2 and anyAcc[k] == 0 or tries[k] >= 8 and nifAcc[k] == 0): keep.add k
    live = keep
    if live.len == 0: break
  let wall = epochTime() - start
  var cnt: seq[string]
  for k, v in counts: cnt.add &"{k}={v}"
  cnt.sort
  let s = &"seed={seed} programs={total} wall_s={int(wall)} cases_per_s={total.float / wall:.1f} " &
          &"distinct_sigs={seen.len} live_shapes={live.len}/{shapes.len} {cnt.join(\" \")}"
  let f = open(outDir / "summary.txt", fmAppend)
  f.writeLine s
  f.close
  echo s

main()
