{.feature: "staticContracts".}
import std/syncio
const K = (-1) shr 1              # folded to 0
proc f(): int =
  var arr = [10, 20, 30, 40]
  let k = (-2) shr 2
  echo "k = ", k                  # -1 at run time
  {.assert: k >= 0 and k <= 3.}   # accepted
  result = arr[(-2) shr 2]        # accepted: reads arr[-1]
var one = 1
echo "const ", K, " runtime ", (-1) shr one
echo f()
