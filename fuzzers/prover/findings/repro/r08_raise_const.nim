{.feature: "staticContracts".}
import std/syncio
proc h(x: int): int {.raises.} =
  var arr = [1, 2, 3, 4]
  var y = 0
  result = 0
  try:
    y = 5
    if x > 3: raise Failure
    y = 0
  except:
    {.assert: y == 0.}
    echo "y = ", y
    result = arr[y]
proc main() =
  try:
    echo h(100)
  except:
    echo "raised"
main()
