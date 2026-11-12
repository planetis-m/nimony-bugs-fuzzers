import std/syncio
type CT = proc (y: int): int {.closure.}

iterator ci(): int {.closure, sideEffect.} =
  var c: CT = proc (y: int): int {.closure.} = y
  yield c(2)
for x in ci(): echo x
