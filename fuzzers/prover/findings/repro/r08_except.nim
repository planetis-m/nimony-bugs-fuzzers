{.feature: "staticContracts".}
import std/syncio
proc risky(x: int) {.raises.} =
  if x > 3: raise Failure
proc f(x: int): int =
  var arr = [1, 2, 3, 4]
  var y = 0
  result = 0
  try:
    y = x
    risky(x)                 # raises: control goes to `except` with y == x
    y = 0
  except:
    {.assert: y == 0.}       # accepted
    echo "in except, y = ", y
    result = arr[y]          # accepted: no check left
echo f(1000000000)
