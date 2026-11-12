{.feature: "staticContracts".}
import std/syncio

proc find(s: seq[int]; x: int): int =
  var idx = -1
  for k in 0 ..< s.len:
    if s[k] == x:
      idx = k
      break
  {.assert: idx >= 0.}      # false when x is not in s
  result = s[idx]           # index "proven": no run-time check is left

echo find(@[10, 20, 30], 20)
echo find(@[10, 20, 30], 99)
