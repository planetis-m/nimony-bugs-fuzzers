# closures fuzzer

Build: `nim c -d:release -o:closures/clofuzz closures/clofuzz.nim`

Usage: `closures/clofuzz --seed:1 --count:100 [--minutes:M] [--avoid:citer-in-citer,unused-local-iter] [--out:DIR] [--work:DIR] [--budget:N] [--noreduce]`
(parallel: several processes with disjoint seed ranges; each needs its own `--work`, default `work/s<seed>`).

Design: `clofuzz.nim` generates random programs over closures, factories, closures in seqs/objects, inline/closure/local
iterators, defer, try/except/finally and raise. Every node both emits Nimony source and runs in a reference interpreter,
so the expected output of every program and every reduced variant is known. Each program is compiled with `nimony c`
and `nimony n` and compared with the model; the first program of each new signature goes to `--out` (default `out/`,
with `log.csv`) and is delta-debugged over its statement tree. See the module comment for the model's rules.

`findings/` holds the 45-minute campaign of the earlier Python version (now in `old/`).
