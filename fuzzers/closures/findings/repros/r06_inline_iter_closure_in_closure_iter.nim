import std/syncio
type CT = proc (y: int): int {.closure.}

iterator it(): int {.sideEffect.} =
  for i in 0 ..< 2:
    var c: CT = proc (y: int): int {.closure.} = y + i
    yield c(1)
iterator ci(): int {.closure, sideEffect.} =
  for x in it():
    yield x
for x in ci(): echo x
