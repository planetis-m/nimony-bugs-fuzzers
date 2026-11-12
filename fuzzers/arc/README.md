# arcfuzz: hexer memory-management fuzzer (ARC + ORC)

Build: `nim c -d:release -o:arc/arcfuzz arc/arcfuzz.nim`
Usage: `arc/arcfuzz --seed:1000 --count:20` (options: `--minutes:M --nimony --out --work --budget:TESTS --sig:SIG --noreduce`).
Parallel: start several processes with disjoint `--seed` ranges (each gets its own `work/s<seed>`).

Design (details in the module doc of `arcfuzz.nim`): random programs over a hook-counting `R(id, v)` whose hooks
check a global alive/dead table, so the program is its own reference model (`ERR`, `LEAK`, `SUMMARY` lines).
Each is built with arc, orc and arc/orc `--opt:speed` (`-d:useLibc`) and run under valgrind; arc vs orc and
base vs opt outputs are diffed. Findings go to `out/s<seed>/` (+ `out/log.csv`); the reducer deletes
statements while one signature persists and writes `reduced.nim`.

`findings/` holds the confirmed bugs, `hand/` their hand-made repros, `old/` the replaced Python fuzzer and its run.
