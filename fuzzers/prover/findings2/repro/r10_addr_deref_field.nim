import std/syncio
type
  Obj = object
    x: int
  Node = ref Obj
proc viaDot(n: Node): ptr int = addr n.x        # accepted
proc viaDeref(n: Node): ptr int = addr n[].x    # Error: invalid expression for `addr` operation
proc viaPtr(p: ptr Obj): ptr int = addr p[].x   # Error
proc whole(p: ptr Obj): ptr Obj = addr p[]      # ?
let n = Node(x: 1)
viaDeref(n)[] = 5
echo n.x
