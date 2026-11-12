import std/[syncio, math]
proc t(p: float32) =
  var a = 3.4e38'f32
  var b = 16777217.0'f32
  var c = 1e-40'f32
  var d = p + 0.1'f32
  echo $float64(a), " ", $float64(b), " ", cast[uint32](c), " ", cast[uint32](d), " ", cast[uint32](sqrt(1e-40'f32))
t(1.0'f32)
