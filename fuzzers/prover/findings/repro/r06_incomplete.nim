{.feature: "staticContracts".}
import std/syncio
type RT = range[0..8]
proc needsRange(x, lo, hi: int): int {.requires: lo <= x and x <= hi.} = x
proc i1(a: int) =
  {.assert: min(a - 2, 7) <= 7.}              # min's own ensures says result <= y
proc i2(a: int; s: seq[int]) =
  {.assert: (max(s.len, a) mod 8) < 8.}
proc i3(x: int): int {.ensures: 0 <= result and result <= 7.} =
  if x < 0: result = 0
  elif x > 7: result = 7
  else: result = x
proc i4(c: int): int =
  {.assume: c > 2.}
  result = needsRange(c, 3, high(int))        # 3 <= c follows from c > 2
proc i5(y: int): int =
  var la = default(array[2..5, int])
  result = 0
  case y
  of 4, 5: result = la[y]
  else: discard
proc i6(): int =
  var r: RT = 0
  inc r
  result = int(r)
proc i7(a: int; s: seq[int]) =
  {.assert: ((high(s) and 15) + 1) > (high(s) and 15).}
echo "ok"
