import std/syncio
proc t(p4: int32) =
  let x: int32 = not (p4 - p4)
  echo x
t(5'i32)
