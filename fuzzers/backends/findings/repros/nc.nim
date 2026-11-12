import std/syncio
proc t(x: int8) =
  var u: uint16 = uint16(not x)
  echo u
t(1'i8)
