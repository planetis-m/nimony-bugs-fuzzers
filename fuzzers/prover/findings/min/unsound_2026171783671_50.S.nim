{.feature: "staticContracts".}
import std/syncio
type
  RT = range[0..8]
  Obj = object
    f, g: int
    cnt: RT
    items: seq[int]
    arr: array[4, int]
proc needsPos(x: int): int {.requires: x > 0.} = x - 1
proc needsRange(x, lo, hi: int): int {.requires: lo <= x and x <= hi.} = x
proc clamp7(x: int): int {.ensures: 0 <= result and result <= 7.} =
  if x < 0: return 0
  if x > 7: return 7
  return x
proc nonNeg(x: int): int {.ensures: result >= 0.} =
  if x < 0: return 0
  return x
proc below(x, lim: int): int {.requires: lim > 0, ensures: 0 <= result and result < lim.} =
  if x < 0: return 0
  if x >= lim: return lim - 1
  return x
proc bump(x: var int) = inc x
proc setTo(x: var int; v: int) = x = v
proc viaPtr(p: ptr int; v: int) = p[] = v
proc shrink(q: var seq[int]) = q.setLen(0)
proc dropOne(q: var seq[int]) =
  if q.len > 0: q.setLen(q.len - 1)
proc clobber(o: var Obj) =
  o.f = o.f * 7 - 3
  o.items.setLen(0)
proc takesRT(x: RT): int = int(x)
proc p6(a, b, c: int; u: uint8; s: seq[int]; t: var seq[int]; o: var Obj; ar: array[8, int]; st: string): int =
  var x = a
  var y = b
  var z = c
  var i = 0
  var j = 0
  var fuel = 0
  var w = u
  var r: RT = 0
  var la = default(array[2..5, int])
  result = 0
  if o.g >= z:
    while (y + 1) < 4:
      inc fuel
      if fuel > 24: return
      while y < o.items.len:
        o.cnt = ((-2) shr 2)
        y = y + 1
      z = ((0 mod 2) and 3)
      while z < st.len:
        {.assert: (z - 1) < st.len.}
        z += 1
      inc y
    j = 0
    while j < t.len:
      z = t[j]
      inc j
    for k1 in 1 .. (8 - 1):
      let p2 = addr y
      break
      i = (o.items.len and 3)
      while ((i + 1) < 6 and la[i] > 3):
        o.g = ar[min(((t.len - 1) - j), (2 + 1))]
        let p3 = addr x
        inc i
  {.assume: o.items.len >= 0.}
  if (((z shr 3) <= 0 and (0 + 1) >= b) and (i shr 1) == 1):
    {.assert: (t.len and 7) <= 7.}
  else:
    discard
  {.assume: (o.items.len - 1) >= 0.}
echo "END"
