# Nimony fuzzers

The fuzzers that found the bugs tracked in this repo's issues. Each is one Nim file in the style of
nimony's `tools/difffuzz.nim`, deterministic from `--seed`. Build with host Nim: `nim c -d:release <file>.nim`.
For parallelism, run several processes with different `--seed` ranges and separate `--out` dirs.

| dir | file | phase under test | oracle |
|---|---|---|---|
| `backends/` | `bfuzz.nim` | C / LLVM / native / JS / wasm backends; constant folding | backends agree (C is the reference); folded constants equal run time |
| `opt/` | `optfuzz.nim` | shoggoth optimizer | same backend with and without `--opt:speed` |
| `arc/` | `arcfuzz.nim` | hexer ARC/ORC (duplifier, destroyer, lifter, mover) | hook-counting model + valgrind |
| `closures/` | `clofuzz.nim` | closures, iterators, lambda lifting | reference interpreter |
| `exc/` | `excfuzz.nim` | exception / control-flow lowering | reference interpreter (try/finally semantics) |
| `prover/` | `provfuzz.nim` | `staticContracts` prover soundness; `--mode:bounds`: check elimination in default mode | proved claims tested at run time; a failing check stops the default and `-d:release` builds as it stops runtimeContracts |
| `nifasm/` | `asmfuzz.nim` | nifasm x86-64 encoder | GNU `as` + objdump |

Each `findings/` holds the write-ups (`NN.md`) and minimized repros of the original 45-minute campaigns
(nimony master 0305d6c6). See each fuzzer's README for usage.
