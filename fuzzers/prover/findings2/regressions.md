# Earlier prover findings (findings/01–08) on nimony master 4ba90a78

Rechecked 2026-11-12 with the repro files of findings/repro/ (copies in work2/reg/), `bin/` built at 4ba90a78,
`bin/nimony c -r --nimcache:nc_<f> <f>.nim`. None of the commits since 0305d6c6 touches the prover
(`git log 0305d6c6..4ba90a78 -- src/nimony/contracts_fir.nim src/nimony/flowtracker.nim src/nimony/controlflow.nim
src/nimony/xints.nim lib/std/system.nim` lists only the reverted expreval pair e832cd59/5a346b5c).

| finding | tracker | repro | result on 4ba90a78 | status |
|---|---|---|---|---|
| 01 for/break exit dropped | fuzzers#14 | r01_forbreak.nim | compiles, prints `20` then `0` (reads `s[-1]`) | **still reproduces** |
|  |  | r01_forbreak_empty.nim | compiles, segfault (exit 139) | still reproduces |
|  |  | r01_forbreak_contradiction.nim | compiles, prints `cnt=10` for a `range[0..8]` field | still reproduces |
| 02 negative `shr` folded toward 0 | fuzzers#16 | r02_negshr.nim | `const 0 runtime -1`, `k = -1`, garbage from `arr[-1]` | **still reproduces** |
| 03 `abs` assumes `result >= 0` | fuzzers#9 | r03_abs.nim | prints `-128`, then garbage (`arr[-128]`) | **still reproduces** |
| 04 write via `addr` arg keeps facts | fuzzers#4 (bug-reports 87) | r04_addrarg.nim | compiles, segfault (exit 139) | **still reproduces** |
| 05 global fact survives a writing call | fuzzers#5 | r05_global.nim | compiles, bus error (exit 135) | **still reproduces** |
| 06 incomplete (six true claims rejected) | fuzzers#24 | r06_incomplete.nim | all six `cannot prove ...` errors, unchanged text | **still reproduces** |
| 07 module name starting with a digit | fuzzers#68 | `01_x.nim` (`echo "hi"`) | `undefined reference to 'main'` at link time | **still reproduces** |
| 08 `except`/`finally` believes the try body ended | fuzzers#15 | r08_except.nim / r08_finally.nim / r08_raise_const.nim | bus error / segfault / `y = 5` + garbage | **still reproduces** |

None is fixed. The v2 run (findings2/log.csv) hits 01, 02, 03, 04, 05 and 08 again from the generator (flavour A,
signatures `forbreak`, `negshr`, `abs`, `addr`, `claim-gv`/`claim-tv`, `try`); those lines are duplicates, not new
bugs (see dedupe.csv).

Related tracker item fixed by 4ba90a78 (not a prover finding of this fuzzer): fuzzers#13 (`func` mutates through a
`ref` via `s[0]` of an immutable seq) is closed; its repro is rejected now. Finding 09 (findings2/09.md) is a
remaining hole of the same rule.
