import std/syncio

type
  CT = proc (y: int): int {.closure, raises.}
  Box = object
    f: CT

iterator u0_it0(a1: int): int {.raises, sideEffect.} =
  discard

proc u1_mk0(a38: int): CT {.raises.} =
  discard
  result = proc (y56: int): int {.closure, raises.} =
    result = 0
    discard

iterator u1_it0(a61: int, a62: int): int {.raises, sideEffect.} =
  discard

iterator u1_it1(a69: int): int {.raises, sideEffect.} =
  discard

iterator u1_it2(a77: int): int {.closure, raises, sideEffect.} =
  discard

proc u2_mk0(a100: int): CT {.raises.} =
  discard
  result = proc (y104: int): int {.closure, raises.} =
    result = 0
    discard

iterator u2_it0(): int {.raises, sideEffect.} =
  discard

iterator u2_it1(a136: int, a137: int): int {.closure, raises, sideEffect.} =
  iterator li143(): int {.closure, raises, sideEffect.} =
    discard

