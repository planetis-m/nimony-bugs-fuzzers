import std/syncio
type CT = proc (y: int): int {.closure.}

proc u() =
  for x in 0 ..< 1:
    let c = proc (y: int): int {.closure.} =
      result = 0
      for i in 0 ..< 2:
        discard
    discard c(0)
u()
