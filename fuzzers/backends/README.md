# bfuzz: differential fuzzer across Nimony backends

    nim c -d:release -o:bin/bfuzz bfuzz.nim
    bin/bfuzz --seed:1000000 --count:100 --out:out --work:work [--backends:c,n,l,j,w] [--time:S] [--noreduce]
    bin/bfuzz --seed:N --emit                    # print the program for one seed

Extended copy of `nimony/tools/difffuzz.nim`: UB-free random programs, every value printed as a bit pattern,
built and run with `nimony c|n|l|j|w` (JS/wasm under node via `run_wasm.js`). C is the oracle; a backend whose
compile, exit or output differs is blamed, or C when all others agree against it. Generator extras: signed
wrapping arithmetic, narrow ints, `keepOverflowFlag` helpers, many-parameter ABI helpers, objects by value,
nested arrays, `case`, `while`/`break`/`continue`, strings. Raw findings go to `<out>/events.csv`; the reducer
deletes statements while the failure persists. Run several processes on disjoint `--seed` ranges for parallelism.

`findings/`: one `NN.md` per distinct bug, `log.csv` (find-rate of the 2026-11-10 run), `repros/`.
`old/`: the campaign's runs, one-off scripts and the original difffuzz.
