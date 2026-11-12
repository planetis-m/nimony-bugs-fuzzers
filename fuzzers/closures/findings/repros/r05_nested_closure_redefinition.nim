import std/syncio
type CT = proc (y: int): int {.closure.}

iterator it(): int {.sideEffect.} =
  yield 1
  yield 2
iterator it2(a: int): int {.sideEffect.} =
  var c: CT = proc (y: int): int {.closure.} =
    var c2: CT = proc (y: int): int {.closure.} = y
    result = c2(y)
  yield c(a)
proc u() =
  for x in it():
    for y in it2(x):
      echo y
u()
