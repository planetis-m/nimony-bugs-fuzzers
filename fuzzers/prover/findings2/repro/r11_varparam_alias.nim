{.feature: "staticContracts".}
{.feature: "assumeSync".}
import std/syncio
type
  Obj = object
    f: int
    items: seq[int]
  Hold = ref object
    o: Obj
var g = 0
proc setG(v: int) = g = v
func shrink(o: var Obj) = o.items.setLen(0)

proc a(n: var int; arr: array[4, int]): int =     # fact about a `var` param, a call writes it
  result = 0
  if n >= 0 and n < 4:
    setG(1000000000)              # `n` is `g` here
    {.assert: n < 4.}             # accepted
    result = arr[n]               # accepted: no check left

proc b(o, q: var Obj): int =                      # fact about one `var` param, a func writes the other
  result = 0
  if o.items.len > 0:
    shrink(q)                     # `q` is `o` (same object behind two refs)
    {.assert: o.items.len > 0.}   # accepted
    echo "len after shrink(q): ", o.items.len
    result = o.items[0]           # accepted: no check left

proc c(n: var int; arr: array[4, int]): int =     # fact about a global, a store to a `var` param
  result = 0
  if g >= 0 and g < 4:
    n = 1000000000                # `n` is `g` here
    {.assert: g < 4.}             # accepted
    result = arr[g]               # accepted

let arr = [1, 2, 3, 4]
g = 1
echo "c: ", c(g, arr)
g = 1
let h1 = Hold(o: Obj(items: @[7]))
let h2 = h1
echo "b: ", b(h1.o, h2.o)
echo "a: ", a(g, arr)
