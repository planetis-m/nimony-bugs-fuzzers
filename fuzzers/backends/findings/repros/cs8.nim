import std/syncio
proc f(x: int8) =
  case x
  of 0: echo "zero"
  of 1, 2: echo "one or two"
  else: echo "other"
f(2'i8)
