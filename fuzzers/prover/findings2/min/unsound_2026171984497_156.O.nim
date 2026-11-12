{.feature: "runtimeContracts".}
{.feature: "assumeSync".}
import std/syncio
type
  RT = int
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
var reached: array[162, bool]
var failed: array[162, bool]
var passed: array[162, bool]
var wit: array[162, bool]
var dead = false
var lastFail = 0
proc fail(id: int) =
  if not dead:
    failed[id] = true
    lastFail = id
    dead = true
proc bad(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = not c
proc ok(id: int; c: bool): bool =
  if not dead:
    reached[id] = true
    if c: passed[id] = true
  if not c: fail(id)
  result = c
proc p14(a, b, c: int; u: uint8; s: seq[int]; t: var seq[int]; o: var Obj; ar: array[8, int]; st: string; n: var int; q: var Obj): int =
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
  if cx < 0:
    discard
  else:
    setCx((st.len - 2))
    if bad(156, not (cx < 0)): return
proc drive14() =
  var ar = default(array[8, int])
  for k in 0 ..< 8: ar[k] = (k * 5) mod 11 - 2
  var ss = [@[1], @[2], @[0, 5, -1], @[7, 1, 3, 0, 2, 8, 4, 6]]
  ss[0].setLen(0)
  let sts = ["", "a", "abcd", "abcdefgh"]
  for a in [low(int), -9, -1, 0, 1, 2, 5, 7, 8, 9, high(int)]:
    for b in [-1, 0, 1, 2, 3, 4, 6, 7, 8, high(int)]:
      for c in [-1, 2, 9]:
        for u in [0'u8, 7'u8, 255'u8]:
          for si in 0 ..< 4:
            dead = false
            var t = ss[(si + 1) mod 4]
            var o = Obj(f: b, g: c, cnt: (si * 2), items: ss[(si + 2) mod 4])
            gv = b
            tv = c
            go = Obj(f: a and 15, g: b, cnt: si, items: ss[(si + 3) mod 4])
            gs = ss[(si + 2) mod 4]
            gp = addr gv
            gb = (if (si and 1) == 0: B() else: D())
            var nn = c
            var qq = Obj(f: c, g: a, items: ss[(si + 1) mod 4])
            let ha = Hold(o: Obj(f: b, g: c, cnt: (si * 2), items: ss[(si + 2) mod 4]))
            let hb = ha
            let al = (si + (c and 3)) mod 3
            var rr = 0
            if al == 0:
              rr = p14(a, b, c, u, ss[si], t, o, ar, sts[(si + c + 1) mod 4], nn, qq)
            elif al == 1:
              rr = p14(a, b, c, u, ss[si], t, ha.o, ar, sts[(si + c + 1) mod 4], gv, hb.o)
            else:
              rr = p14(a, b, c, u, ss[si], t, o, ar, sts[(si + c + 1) mod 4], tv, go)
            discard rr
            if dead and not wit[lastFail]:
              wit[lastFail] = true
              echo "W ", lastFail, " a=", a, " b=", b, " c=", c, " u=", u, " si=", si
drive14()
for i in 0 ..< 162:
  if reached[i]: echo "R ", i
  if passed[i]: echo "P ", i
  if failed[i]: echo "F ", i
echo "END"
