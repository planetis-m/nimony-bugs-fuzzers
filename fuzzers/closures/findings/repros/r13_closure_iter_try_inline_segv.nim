import std/syncio
type CT = proc (y: int): int {.closure, raises.}

proc mk(a: int): CT {.raises.} =
  result = proc (y: int): int {.closure, raises.} = a + y

iterator it(): int {.raises, sideEffect.} =
  for i in 0 ..< 3:
    var c: CT = mk(5)
  yield 1

iterator ci(): int {.closure, raises, sideEffect.} =
  for x in it():
    try:
      for y in it():
        discard
    except ErrorCode:
      var c: CT = mk(7)
  yield 2

proc u() {.raises.} =
  for x in ci():
    echo x

try:
  u()
except ErrorCode as e:
  echo "exc ", e
echo "end"
