# bfuzz: differential fuzzer across Nimony backends

    nim c -d:release -o:bin/bfuzz bfuzz.nim
    bin/bfuzz --seed:1000000 --count:100 --out:out --work:work [--backends:c,n,l,j,w] [--minutes:M] [--noreduce]
    bin/bfuzz --seed:N --emit                    # print the program for one seed

Extended copy of `nimony/tools/difffuzz.nim`: UB-free random programs, every value printed as a bit pattern,
built and run with `nimony c|n|l|j|w` (JS/wasm under node via `run_wasm.js`). C is the oracle; a backend whose
compile, exit or output differs is blamed, or C when all others agree against it. Generator extras: signed
wrapping arithmetic, narrow ints, `keepOverflowFlag` helpers, many-parameter ABI helpers, objects by value,
nested arrays, `case`, `while`/`break`/`continue`, strings. Raw findings go to `<out>/events.csv`; the reducer
deletes statements while the failure persists. Run several processes on disjoint `--seed` ranges for parallelism.

Folding: every `t<i>` has an `f<i>` of four constant expressions printed as a `const`, a `let` and at run time
(literals behind `{.noinline.}` identities); the three must agree on every backend. The generator evaluates integer
expressions exactly and avoids the documented compile error (signed overflow) and out-of-range conversions to a signed
type, so a refused `const` is a finding (`fold:compileFails:<error> [<what wraps>]`). A `float32` difference that
only comes from folding at "maximum precision" (documented, as in Nim 2) is counted in the summary, not reported; one
that rounding the `float32` literals first cures is `fold:mismatch:… [f32lit]`. Fold findings are reduced by shrinking
the one expression.

`findings/`: one `NN.md` per distinct bug, `log.csv` (find-rate of the 2026-11-10 run), `repros/`.
