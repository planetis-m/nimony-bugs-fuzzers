import std/syncio
type CT = proc (y: int): int {.closure, raises.}
proc mk(a: int): CT {.raises.} =
  iterator li(p: int): int {.closure, raises, sideEffect.} =
    var s: seq[CT] = @[]
    var v = a + p
    if s.len > 1: v = s[1](12)
    yield v
  result = proc (y: int): int {.closure, raises.} =
    result = y
  for x in li(1): echo x
try: echo mk(4)(1)
except: echo "exc"
