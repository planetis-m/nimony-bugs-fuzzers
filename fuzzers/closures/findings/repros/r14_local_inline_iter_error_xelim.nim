import std/syncio
type CT = proc (y: int): int {.closure.}
type Box = object
  f: CT
proc u(a: int) =
  var b = Box(f: proc (y: int): int {.closure.} = y)
  iterator li(): int {.sideEffect.} =
    yield b.f(a)
  for x in li(): echo x
u(3)
