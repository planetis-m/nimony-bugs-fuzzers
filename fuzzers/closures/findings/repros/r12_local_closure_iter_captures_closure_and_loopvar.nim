import std/syncio
type CT = proc (y: int): int {.closure.}

iterator it(n: int): int {.sideEffect.} = yield n
proc u(p: int) =
  for x in it(p):
    var c: CT = proc (y: int): int {.closure.} = y * 2
    iterator li(a: int): int {.closure, sideEffect.} =
      yield c(a + x)
    for y in li(3): echo y
u(1)
