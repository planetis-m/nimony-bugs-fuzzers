# Signature -> finding map (campaign seed 5000, 45 min, 2174 programs, 46 signatures)

Confirmed with a hand-written repro: f01->03, f02->08, f06->07 (variant), f08->15, f09->01, f10->09, f11->06,
f12->05, f13->04, f14->02, f15/f19/f20/f30/f31/f35/f38/f41->10 (same eraiser tuple projection, judged by C error
shape), f17->12, f22/f23/f24->13, f03->11 (same assertion).

The tool reduced these, but I did not triage them by hand (raw/<dir>/min.nim): f04 `ii.N`, f05 `llTemp.N`, f07 `lf.N`,
f16 invalid initializer, f18 nimony_model isTagLit, f21 closureTuple assigned to int, f25 `this.N`, f26 duplifier (dot ...).
Hand-written variants of f05/f07/f16 that use the local iterator compile fine. These may be variants of 02 (an unused
capturing local closure iterator) that the reducer reached by deleting the use.

Not reduced: f27-f29, f32-f34, f36, f37, f39, f40, f42-f46 (eraiser `callee type not params`, trackers assertion,
`statement not eliminated: for`, native-only f33, `llRes` undeclared, iterVal/init argument types).

Earlier runs, aborted after 1-2 min and kept for honesty in ../findings_aborted/: run 1 had oversized programs, run 2 had a model bug
(a `defer` in a factory's prologue ran too early). The campaign was restarted from scratch after each.
