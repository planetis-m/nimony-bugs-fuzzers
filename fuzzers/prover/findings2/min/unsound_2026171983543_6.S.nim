{.feature: "staticContracts".}
{.feature: "assumeSync".}
import std/syncio
type
  RT = range[0..8]
  Obj = object
    f, g: int
    cnt: RT
    items: seq[int]
    arr: array[4, int]
proc needsPos(x: int): int {.requires: x > 0.} = x - 1
proc needsRange(x, lo, hi: int): int {.requires: lo <= x and x <= hi.} = x
proc clamp7(x: int): int {.ensures: 0 <= result and result <= 7.} =
  if x < 0: return 0
  if x > 7: return 7
  return x
proc nonNeg(x: int): int {.ensures: result >= 0.} =
  if x < 0: return 0
  return x
proc below(x, lim: int): int {.requires: lim > 0, ensures: 0 <= result and result < lim.} =
  if x < 0: return 0
  if x >= lim: return lim - 1
  return x
proc bump(x: var int) = inc x
proc setTo(x: var int; v: int) = x = v
proc viaPtr(p: ptr int; v: int) = p[] = v
proc shrink(q: var seq[int]) = q.setLen(0)
proc dropOne(q: var seq[int]) =
  if q.len > 0: q.setLen(q.len - 1)
proc clobber(o: var Obj) =
  o.f = o.f * 7 - 3
  o.items.setLen(0)
proc takesRT(x: RT): int = int(x)
type
  B = ref object of RootObj
  D = ref object of B
  Hold = ref object
    o: Obj
var gv = 0
var tv {.threadvar.}: int
var go = Obj()
var gs: seq[int] = @[]
var gp: ptr int = addr gv
var gb: B = B()
proc setGv(v: int) = gv = v
proc bumpGv() = inc gv
proc setTv(v: int) = tv = v
proc touchGo() =
  go.f = go.f * 7 - 3
  go.items.setLen(0)
proc clearGs() = gs.setLen(0)
proc pokeP(v: int) = gp[] = v
proc stash(p: ptr int) = gp = p
method poke(b: B; v: int) {.base.} = gv = v
method poke(d: D; v: int) =
  go.f = v
  tv = v
proc mixG(x: var int) =
  inc x
  gv = gv * 3 + 1
var gfn: proc (v: int) {.closure.} = setTv
func fbump(x: var int) = inc x
func fset(x: var int; v: int) = x = v
func fclob(o: var Obj) =
  o.f = o.f * 5 + 1
  o.items.setLen(0)
func fadd(s: var seq[int]; v: int) = s.add v
proc risky(x: int) {.raises.} =
  if x > 3: raise Failure
proc p0(a, b, c: int; u: uint8; s: seq[int]; t: var seq[int]; o: var Obj; ar: array[8, int]; st: string; n: var int; q: var Obj): int =
  var x = a
  var y = b
  var z = c
  var i = 0
  var j = 0
  var fuel = 0
  var w = u
  var r: RT = 0
  var la = default(array[2..5, int])
  result = 0
  var cx = c
  proc setCx(v: int) {.closure.} = cx = v
  var fn: proc (v: int) {.closure.} = setCx
  gp = addr gv
  if n >= st.len:
    return
  setGv(1000000000)
  {.assert: not (n >= st.len).}
echo "END"
