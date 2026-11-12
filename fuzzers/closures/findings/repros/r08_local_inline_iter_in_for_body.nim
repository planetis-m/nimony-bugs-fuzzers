import std/syncio
type CT = proc (y: int): int {.closure.}

iterator it(): int {.sideEffect.} = yield 1
proc u() =
  for x in it():
    iterator li(a: int): int {.sideEffect.} =
      yield a
    for y in li(x): echo y
u()
