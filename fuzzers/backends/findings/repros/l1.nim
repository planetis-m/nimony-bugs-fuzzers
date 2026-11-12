import std/syncio
proc t(x: int64) =
  var a5: int64 = int64(uint32(x))
  var b: int32 = int32(int8(x))
  echo a5, " ", b
t(-1'i64)
var g = int64(uint32((-1'i64)))
echo g
