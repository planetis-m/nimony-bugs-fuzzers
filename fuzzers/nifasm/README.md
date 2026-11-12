# nifasm x86-64 differential fuzzer

    nim c -d:release -o:nifasm/asmfuzz nifasm/asmfuzz.nim
    nifasm/asmfuzz --seed:1 --minutes:45 [--out:DIR] [--work:DIR]   # or --count:N

Random instructions (mnemonic x operand shape, sometimes a short sequence) go to nifasm as `(lenient)` procs and to
GNU `as --64` in Intel syntax; bytes are compared, and differences are compared again after `objdump -M intel`
normalisation. Verdicts: mismatch, accepts-invalid, rejects-valid, hazard (div/idiv divisor in rdx).
One nifasm, one `as` and one objdump run per 64-case batch (cases fenced by `mov r11, MAGIC+i` markers).
Shapes nobody accepts are retired at runtime (replaces the old probe matrix). Findings are minimized and logged to
`DIR/log.csv`, `DIR/findings.txt`, `DIR/summary.txt` (default `asmfuzz.out`). Design notes: top of `asmfuzz.nim`.

`findings/` holds the 45-minute campaign of the old Python fuzzer (now in `old/`); `findings/run_repros.sh` re-checks its repros.
