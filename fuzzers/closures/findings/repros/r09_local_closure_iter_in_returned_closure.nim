import std/syncio
type CT = proc (y: int): int {.closure.}

proc mk(a: int): CT =
  iterator li(p: int): int {.closure, sideEffect.} =
    yield p
  result = proc (y: int): int {.closure.} =
    result = 0
    for x in li(a + y):
      result = x
echo mk(4)(1)
