# excfuzz — exception / control-flow lowering fuzzer (desugar, xelim, eraiser)

Build: `nim c -d:release -o:exc/excfuzz exc/excfuzz.nim`

Usage: `exc/excfuzz --seed:1000 --count:50 [--minutes:M]` (`--one:SEED` prints a program and its expected trace;
`--allow:1234` re-enables shapes of known findings 01-05; `--budget:0` skips reduction).

Design: one file. A random program tree (try/except/finally, defer, raise/re-raise, return/break/continue in try
and finally, string case, if/case/try expressions, object defaults) is rendered to Nim and interpreted with Nim's
try/finally semantics, so the expected output is exact. Oracle: `nimony c`, `c --opt:speed` and `n` must print
that trace. A new failure signature is reduced by deleting procs/statements/arms, unwrapping and shrinking
expressions. Output in `out/` (`<seed>_<cfg>[.min].nim`, `log.csv`). Parallelism: several processes, different
`--seed`. Findings: `findings/NN.md`.
