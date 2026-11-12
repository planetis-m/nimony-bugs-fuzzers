import std/syncio
type CT = proc (y: int): int {.closure.}

iterator it(): int {.sideEffect.} =
  iterator li(): int {.closure, sideEffect.} =
    yield 5
  for x in li(): yield x
iterator ci(): int {.closure, sideEffect.} =
  for x in it():
    yield x
for x in ci(): echo x
