import std/[syncio, math]
type B = object
  q: array[4, uint64]
  d: float64
  e: int8
proc t7(p0: uint64; p1: float64; p2: uint32; p3: float32; p4: int32) =
  var a0: uint64 = p0
  var a4: int32 = 0'i32
  var b0 = B(q: [p0, p0 xor 1'u64, 0x7FFFFFFFFFFFFFFF'u64, 9'u64], d: p1, e: (-100'i8))
  var mat: array[3, array[4, int32]] = [[p4, 1'i32, -2'i32, 3'i32], [(not (1'i32)), p4 * 3'i32, 0'i32, high(int32)], [low(int32), 7'i32, p4 - 1'i32, int32(a4)]]
  mat[(b0.q[3]) mod 3'u64][((uint64((1'i16)) and (a0 mod (0x0000000000000002'u64 or 1'u64)))) and 3'u64] = int32(uint8((p0 mod (0x0000000100000000'u64 or 1'u64)) and 255'u64))
  echo "t7 ", cast[uint32](mat[0][0])
proc main() =
  t7(0x8000000000000000'u64, -1e300, 0xADB6C093'u32, 0.0'f32, (0'i32))
main()