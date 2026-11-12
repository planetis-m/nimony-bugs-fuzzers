import std/syncio

iterator outer(): int {.closure, sideEffect.} =
  iterator inner(): int {.closure, sideEffect.} =
    discard
  yield 2

for x in outer():
  echo x
