{.feature: "runtimeContracts".}
{.feature: "assumeSync".}
import std/syncio
type
  RT = int
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
var reached: array[156, bool]
var failed: array[156, bool]
var passed: array[156, bool]
var wit: array[156, bool]
var dead = false
var lastFail = 0
proc fail(id: int) =
  if not dead:
    failed[id] = true
    lastFail = id
    dead = true
proc bad(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = not c
proc ok(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = c
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
        if bad(50, (((-2) shr 2) >= 0 and ((-2) shr 2) <= 8)): return
        o.cnt = ((-2) shr 2)
        y = y + 1
      z = ((0 mod 2) and 3)
      while z < st.len:
        if bad(52, (z - 1) < st.len): return
        z += 1
      inc y
    j = 0
    while j < t.len:
      if bad(54, (j >= 0 and j < t.len)): return
      z = t[j]
      inc j
    for k1 in 1 .. (8 - 1):
      let p2 = addr y
      break
      i = (o.items.len and 3)
      while ((i + 1) < 6 and (ok(55, (i >= 2 and i < 6)) and la[i] > 3)):
        if bad(57, (min(((t.len - 1) - j), (2 + 1)) >= 0 and min(((t.len - 1) - j), (2 + 1)) < 8)): return
        o.g = ar[min(((t.len - 1) - j), (2 + 1))]
        let p3 = addr x
        inc i
  if not (o.items.len >= 0): (dead = true; return)
  if (((z shr 3) <= 0 and (0 + 1) >= b) and (i shr 1) == 1):
    if bad(59, (t.len and 7) <= 7): return
  else:
    discard
  if not ((o.items.len - 1) >= 0): (dead = true; return)
proc drive6() =
  var ar = default(array[8, int])
  for k in 0 ..< 8: ar[k] = (k * 5) mod 11 - 2
  var ss = [@[1], @[2], @[0, 5, -1], @[7, 1, 3, 0, 2, 8, 4, 6]]
  ss[0].setLen(0)
  let sts = ["", "a", "abcd", "abcdefgh"]
  for a in [low(int), -9, -1, 0, 1, 2, 5, 7, 8, 9, high(int)]:
    for b in [-1, 0, 1, 2, 3, 4, 6, 7, 8, high(int)]:
      for c in [-1, 2, 9]:
        for u in [0'u8, 7'u8, 255'u8]:
          for si in 0 ..< 4:
            dead = false
            var t = ss[(si + 1) mod 4]
            var o = Obj(f: b, g: c, cnt: (si * 2), items: ss[(si + 2) mod 4])
            let rr = p6(a, b, c, u, ss[si], t, o, ar, sts[(si + c + 1) mod 4])
            discard rr
            if dead and not wit[lastFail]:
              wit[lastFail] = true
              echo "W ", lastFail, " a=", a, " b=", b, " c=", c, " u=", u, " si=", si
drive6()
for i in 0 ..< 156:
  if reached[i]: echo "R ", i
  if passed[i]: echo "P ", i
  if failed[i]: echo "F ", i
echo "END"
