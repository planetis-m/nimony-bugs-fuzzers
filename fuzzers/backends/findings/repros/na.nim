import std/syncio
proc t(p0: uint64) =
  var arr: array[2, uint64] = [p0, p0 + 1'u64]
  let a = float64(arr[1])
  let b = float64(p0)
  echo cast[uint64](a), " ", cast[uint64](b)
t(0x8000000000000005'u64)
