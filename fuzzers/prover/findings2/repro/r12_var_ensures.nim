{.feature: "staticContracts".}
import std/syncio
func setPos(x: var int) {.ensures: x >= 0.} =
  if x < 0: x = 0
func setPos2(x: var int) {.ensures: x >= 0.} =
  x = 5
func retPos(x: int): int {.ensures: result >= 0.} =
  if x < 0: return 0
  return x
proc t1(a: int) =
  var i = a
  setPos(i)
  {.assert: i >= 0.}
proc t2(a: int) =
  var i = a
  setPos2(i)
  {.assert: i >= 0.}
proc t3(a: int) =
  var i = a
  var y = a
  if i >= 0 and i < 4:
    setPos(y)
    {.assert: i < 4.}
proc t4(a: int) =
  let i = retPos(a)
  {.assert: i >= 0.}
t1(1); t2(1); t3(1); t4(1)
