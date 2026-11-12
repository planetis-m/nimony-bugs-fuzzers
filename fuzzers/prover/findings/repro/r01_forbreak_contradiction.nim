{.feature: "staticContracts".}
import std/syncio
type
  RT = range[0..8]
  Obj = object
    cnt: RT
proc f(o: var Obj): int =
  var arr = [1, 2, 3]
  for k in 2 .. 0:          # never entered
    break
  inc(o.cnt, 2)             # accepted: cnt becomes 10 in a range[0..8]
  result = arr[int(o.cnt)]  # accepted: arr[10] of a 3-element array
var o = Obj(cnt: 8)
echo f(o), " cnt=", o.cnt
