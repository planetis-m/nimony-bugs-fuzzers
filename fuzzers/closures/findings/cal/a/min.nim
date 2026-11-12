import std/syncio

type
  CT = proc (y: int): int {.closure, raises.}
  Box = object
    f: CT

iterator u2_it0(a109: int): int {.raises, sideEffect.} =
  try:
    var c112: CT = proc (y113: int): int {.closure, raises.} =
      result = 0
      iterator li114(a115: int): int {.closure, raises, sideEffect.} =
        var v116 = ((a115 * ((a115 + a115) mod 997)) mod 997)
        yield ((((12 * y113) mod 997) + 997 - ((v116 * y113) mod 997)) mod 997)
  except ErrorCode as e119:
    discard

iterator u2_it1(): int {.closure, raises, sideEffect.} =
  discard

proc u2(p0, p1: int) {.raises.} =
  for x154 in u2_it0(((p1 + 4) mod 997)):
    discard

try:
  u2(2, 4)
except ErrorCode as e:
  echo "u2 exc ", e
