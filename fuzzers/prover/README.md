# provfuzz: soundness fuzzer for Nimony's contract prover (`staticContracts`)

Build: `nim c -d:release -o:prover/provfuzz prover/provfuzz.nim`

Usage: `prover/provfuzz --seed:1 --count:20 [--minutes:45] [--mode:bounds] [--out:DIR] [--work:DIR] [--budget:150] [--noreduce] [--nimony:PATH]`
(run several processes with different seed ranges for parallelism; findings + `log.csv` go to `--out`, default `prover/out/`).
Cap memory per process (children inherit it): `prlimit --as=4294967296 prover/provfuzz ...`

Design (details in the doc comment at the top of `provfuzz.nim`):

* Generator: modules of 16 random procs (statement trees, difffuzz style) with guards, loops, index arithmetic,
  `var`/`ptr`/shared-state writes and claims (`{.assert.}`, indexes, `.requires`, ranges, `.ensures`).
  seed mod 3: 0 = flavour A (shared state and known-bug constructs on), 1 = flavour C (owned state only),
  2 = `func`-rule module (40 routines, legality from the doc rule, judged by `nimony check`).
* Oracle: settle under staticContracts (delete every rejected claim until it compiles), then run the proved
  claims as run-time tests on ~4000 inputs: proved-but-fails = unsound. Also false-violation, incomplete
  (`incomplete.log`), crash.
* `--mode:bounds`: bounds-check elimination in the default contract mode. Run-time checks only (no assert, assume,
  ensures or range), plus stores of extreme values (fuzzers#93) and, in flavour A, `for` bounds the body writes
  (llms#164). Mode O finds a witness for every failing check; it replays in runtimeContracts (every check kept) and in
  the default and `-d:release` builds. A build whose output differs ran past the check: `unchecked/<flavour>:<check>:<tags> [<builds>]`.
* Classifier: signature = flavour, claim kind, shared variables named, known-bug constructs present.
* Reducer: delta debugging over the statement tree and sub-expressions; writes `*.reduced.nim`.

`findings/`, `findings2/`: the earlier runs (bugs 01-12). `old/`: the Python versions (v1, v2) and scratch dirs.
