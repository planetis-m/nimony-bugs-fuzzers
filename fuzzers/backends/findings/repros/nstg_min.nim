type V = object
  x, y: float64
  n: uint32
type S = object
  a: int16
  b: int8
  c: float32
type B = object
  q: array[4, uint64]
  d: float64
  e: int8
proc sumMat(m: array[3, array[4, int32]]): int32 =
  m[0][1] + m[1][2] * m[2][3] - m[2][0]
proc h4(q0: float32; q1: bool; q2: float64; q3: float64; q4: S; q5: uint8; q6: uint32; q7: uint64; q8: bool; q9: float64; q10: int64; q11: uint64; q12: float64; q13: V; q14: B; q15: V): S =
  let mixv = ((uint64((if q0 != q0: 0x7fc00000'u32 else: cast[uint32](q0))) * 3'u64) xor (uint64(ord(q1)) * 5'u64) xor ((if q2 != q2: 0x7ff8000000000000'u64 else: cast[uint64](q2)) * 7'u64) xor ((if q3 != q3: 0x7ff8000000000000'u64 else: cast[uint64](q3)) * 9'u64) xor ((uint64(cast[uint16](q4.a)) xor (uint64(cast[uint8](q4.b)) shl 16) xor (uint64((if q4.c != q4.c: 0x7fc00000'u32 else: cast[uint32](q4.c))) shl 24)) * 11'u64) xor (uint64(q5) * 13'u64) xor (uint64(q6) * 15'u64) xor (uint64(q7) * 17'u64) xor (uint64(ord(q8)) * 19'u64) xor ((if q9 != q9: 0x7ff8000000000000'u64 else: cast[uint64](q9)) * 21'u64) xor (cast[uint64](q10) * 23'u64) xor (uint64(q11) * 25'u64) xor ((if q12 != q12: 0x7ff8000000000000'u64 else: cast[uint64](q12)) * 27'u64) xor (((if q13.x != q13.x: 0x7ff8000000000000'u64 else: cast[uint64](q13.x)) xor uint64(q13.n)) * 29'u64) xor ((q14.q[0] xor q14.q[3] xor (if q14.d != q14.d: 0x7ff8000000000000'u64 else: cast[uint64](q14.d)) xor uint64(cast[uint8](q14.e))) * 31'u64) xor (((if q15.x != q15.x: 0x7ff8000000000000'u64 else: cast[uint64](q15.x)) xor uint64(q15.n)) * 33'u64))
  S(a: int16(mixv), b: int8(mixv shr 16), c: float32(mixv shr 40))
proc t7(p0: uint64; p1: float64; p2: uint32; p3: float32; p4: int32) =
  var a0: uint64 = 0'u64
  var a1: uint64 = 0'u64
  var a4: int32 = 0'i32
  var a5: int64 = 0'i64
  var a8: float32 = 0.0'f32
  var a9: bool = false
  var v = V(x: 0.0, y: 0.0, n: 0'u32)
  var w = V(x: 0.0, y: 0.0, n: 0'u32)
  var arr: array[8, uint64] = [p0 + 0'u64, p0 + 1'u64, p0 + 2'u64, p0 + 3'u64, p0 + 4'u64, p0 + 5'u64, p0 + 6'u64, p0 + 7'u64]
  var s0 = S(a: (-32768'i16), b: (-1'i8), c: float32(a4))
  var s1 = S(a: int16(p4), b: int8(p2), c: p3)
  var b0 = B(q: [p0, p0 xor 1'u64, a0, 9'u64], d: p1, e: int8(a4))
  var mat: array[3, array[4, int32]] = [[p4, 1'i32, -2'i32, 3'i32], [int32(a1), p4 * 3'i32, 0'i32, high(int32)], [low(int32), 7'i32, p4 - 1'i32, a4]]
  var sb = ""
  s1 = h4((if (a8 != a8): (if (sb.len > 5): p3 else: a8) else: float32(sumMat(mat))), (not ((sb.len > 5) and (sb.len mod 3 == 1))), p1, float64((if a9: p3 else: s0.c)), s1, uint8((0x7E9B58E3'u32 xor p2) and 255'u32), (p2 div (w.n or 1'u32)), arr[(p0) and 7'u64], ((not sumMat(mat)) != (mat[(a0 mod 3'u64)][(p0 and 3'u64)] mod (((-2'i32) and 63'i32) + 1'i32))), w.x, a5, (not (0x0000000080000000'u64 and a0)), v.x, w, b0, w)
proc main() =
  t7(0x0000000000000000'u64, 2.5, 0x00000005'u32, 0.5'f32, (-1000'i32))
main()