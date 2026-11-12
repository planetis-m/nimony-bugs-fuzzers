import std/syncio

proc main() =
  let c = proc (y: int): int {.closure.} =
    result = 0
    iterator li(): int {.closure, sideEffect.} =
      yield y
  echo c(1)
main()
