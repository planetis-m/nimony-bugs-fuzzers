import std/syncio
iterator a(n: int): int {.closure, raises, sideEffect.} =
  yield n
iterator b(n: int): int {.closure, raises, sideEffect.} =
  yield n * 10
proc u() {.raises.} =
  for x in a(1):
    for y in b(x + 1):
      echo y
try: u()
except: echo "exc"
