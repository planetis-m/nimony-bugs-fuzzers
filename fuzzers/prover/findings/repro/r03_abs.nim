{.feature: "staticContracts".}
import std/syncio
proc f(x: int8): int =
  var arr = [1, 2, 3, 4]
  let y = abs(x)
  {.assert: y >= 0.}              # accepted; false for x = -128
  result = 0
  if y < 4: result = arr[int(y)]  # accepted: reads arr[-128]
var v = low(int8)
echo abs(v)
echo f(v)
