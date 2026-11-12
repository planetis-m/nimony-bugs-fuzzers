import std/syncio
proc f(x: int64) =
  case x
  of 0: echo "zero"
  else: echo "other"
f(0'i64)
