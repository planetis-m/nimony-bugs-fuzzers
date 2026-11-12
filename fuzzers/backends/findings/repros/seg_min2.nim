import std/syncio
type B = object
  q: array[4, uint64]
  d: float64
  e: int8
proc t6(p0: uint64; p1: float64; p2: uint32; p3: float32; p4: int32) =
  var a0: uint64 = 0x8000000000000000'u64
  var a1: uint64 = uint64(ord((32767'u16 <= 1'u16)))
  var a3: uint8 = 0'u8
  var a4: int32 = p4
  var i32v: int32 = p4
  var i64v: int64 = int64(a3)
  var b0 = B(q: [p0, p0 xor 1'u64, (a1 + p0), 9'u64], d: p1, e: (-100'i8))
  var b1 = b0
  var mat: array[3, array[4, int32]] = [[p4, 1'i32, -2'i32, 3'i32], [p4, p4 * 3'i32, 0'i32, high(int32)], [low(int32), 7'i32, p4 - 1'i32, ((-1000'i32) mod (((2'i32) and 63'i32) + 1'i32))]]
  var sb = ""
  for k0 in 0 ..< 5:
    a0 = (((not b1.q[(a0 and 3'u64)]) shr ((0x0000000080000000'u64 + p0) and 63'u64)) xor (a1 mod (cast[uint64](i64v) or 1'u64)))
  a4 = (int32(uint64(ord((sb.len > 5)))) - ((i32v - mat[(a0 mod 3'u64)][(p0 and 3'u64)]) + (-((1'i32)))))
  echo a0, " ", a0 mod 3'u64, " ", a4
proc main() =
  t6(0x0000000000000002'u64, 4294967296.0, 0x00000002'u32, -0.25'f32, (-1000'i32))
main()