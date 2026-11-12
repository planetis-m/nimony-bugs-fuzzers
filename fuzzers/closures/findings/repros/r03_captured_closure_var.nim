import std/syncio
type CT = proc (y: int): int {.closure.}

proc main(a: int) =
  var c2: CT = proc (y: int): int {.closure.} = y + 1
  let c: CT = proc (y: int): int {.closure.} =
    result = c2(a)
  echo c2(a)
  echo c(0)
main(4)
