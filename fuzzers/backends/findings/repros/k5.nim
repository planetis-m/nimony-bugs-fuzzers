import std/syncio
proc ck(a, b: int16): int16 =
  {.keepOverflowFlag.}:
    result = a - b
proc t(i16v: int16) =
  var u = ck(i16v, i16v)
  echo u
t(5'i16)
