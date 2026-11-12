{.feature: "staticContracts".}
import std/syncio
proc risky(x: int) {.raises.} =
  if x > 3: raise Failure
proc f(x: int): int {.raises.} =
  var arr = [1, 2, 3, 4]
  var y = 0
  result = 0
  try:
    y = x
    risky(x)                 # raises: control goes to `finally` with y == x
    y = 0
  finally:
    {.assert: y == 0.}       # accepted
    echo "in finally, y = ", y
    echo arr[y]              # accepted: no check left
proc main() =
  try:
    echo f(1000000000)
  except:
    echo "raised"
main()
