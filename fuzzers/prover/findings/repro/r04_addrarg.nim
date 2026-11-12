{.feature: "staticContracts".}
import std/syncio
type Obj = object
  f: int
proc viaPtr(p: ptr int; v: int) = p[] = v
proc g(o: var Obj; s: seq[int]): int =
  result = 0
  if o.f >= 0 and o.f < s.len:
    viaPtr(addr o.f, 1000000000)
    {.assert: o.f < s.len.}       # accepted
    result = s[o.f]               # accepted: no check left
var o = Obj(f: 1)
echo g(o, @[1, 2, 3])
