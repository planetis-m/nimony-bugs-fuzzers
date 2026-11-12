# nimony-bugs-fuzzers

Bugs in [Nimony](https://github.com/nim-lang/nimony) found by fuzzing, and the fuzzers that found them.

- **Issues** are the bug reports: one per distinct bug, with a minimized repro.
- **`fuzzers/`** holds seven fuzzers, one Nim file each, in the style of nimony's `tools/difffuzz.nim`:
  backends, optimizer, ARC/ORC, closures, exceptions, the `staticContracts` prover, and the nifasm
  encoder. Each directory has a README and `findings/` with write-ups and repros. See
  [`fuzzers/README.md`](fuzzers/README.md).

Build and run one (host Nim 2.x, a built nimony):

    nim c -d:release fuzzers/backends/bfuzz.nim
    fuzzers/backends/bfuzz --seed:1 --count:20 --nimony:/path/to/nimony/bin/nimony

Runs are deterministic from `--seed`; for parallelism start several processes with different seed
ranges and separate `--out` dirs.

## Closing issues

A nimony PR or commit that says `Fixes planetis-m/nimony-bugs-fuzzers#N` closes issue N here once it is
merged: `.github/workflows/close-fixed.yml` runs `scripts/close_fixed.py` hourly.
