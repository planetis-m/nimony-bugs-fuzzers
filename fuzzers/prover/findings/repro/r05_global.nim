{.feature: "staticContracts".}
{.feature: "assumeSync".}
import std/syncio
var g = 0
proc setg() = g = 1000000000
proc f(): int =
  var arr = [1, 2, 3, 4]
  result = 0
  if g >= 0 and g < 4:
    setg()                    # writes the global
    {.assert: g < 4.}         # accepted
    result = arr[g]           # accepted: no check left
echo f()
