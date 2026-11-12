{.feature: "staticContracts".}
import std/syncio
proc f(n: int; s: seq[int]): int =
  result = 0
  for k in 0 ..< s.len:
    if s[k] == 3: break
  result = s[0]
echo f(0, @[])
