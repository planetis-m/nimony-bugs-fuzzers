import std/syncio

type
  CT = proc (y: int): int {.closure, raises.}
  Box = object
    f: CT

iterator u0_it0(a1: int, a2: int): int {.raises, sideEffect.} =
  var v3 = a1
  var v4 = ((a2 + v3) mod 997)
  var c5: CT = proc (y6: int): int {.closure, raises.} =
    result = 0
    discard
  try:
    iterator li10(a11: int, a12: int): int {.closure, raises, sideEffect.} =
      v4 = c5(((2 + 997 - 10) mod 997))
    for x13 in li10(((v4 * v4) mod 997), ((10 + 997 - a2) mod 997)):
      discard
  except ErrorCode as e14:
    discard

iterator u0_it1(a19: int, a20: int): int {.closure, raises, sideEffect.} =
  for x22 in u0_it0(a19, ((a20 + 997 - a19) mod 997)):
    discard

