# optfuzz: shoggoth optimizer differential fuzzer

    nim c -d:release -o:optfuzz optfuzz.nim
    ./optfuzz --seed:1 --count:50 --out:out --work:work [--mode:n] [--time:S] [--noreduce]
    ./optfuzz --seed:N --emit                    # print the program for one seed

Oracle: the same backend with and without the optimizer (`nimony c` vs `nimony c --opt:speed`; `--mode:n` for
native). Generator: difffuzz's UB-free one plus globals written by callees, `var` params (a global passed as the
var arg), `ptr` params that may alias, `addr` of locals/array elements/fields/globals, `.inline`/`.noinline`
helpers with early returns, recursion, `while`/`for`/labelled `block` with `break`/`continue`, `case`, checked
`int` arithmetic and (rarely) checked indexing. A finding is triaged by rerunning the opt build once per
`SHOGGOTH_DISABLE=<pass>`; those passes join its signature and only a new signature is reduced.
Raw findings go to `<out>/log.csv`. Parallelism: several processes on disjoint `--seed` ranges.

`findings/`: one `NN.md` per distinct bug, `log.csv` (2026-11-10 run). `old/`: runs, scripts, `min/` hand repros.
