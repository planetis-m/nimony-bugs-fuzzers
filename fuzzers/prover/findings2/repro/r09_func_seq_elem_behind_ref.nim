import std/syncio
type
  NodeObj = object
    s: seq[int]
  Node = ref NodeObj
  Holder = object
    r: Node
func fb(x: var int) = inc x
func viaInc(n: Node) = inc n.s[0]           # n.s is behind the ref
func viaVarArg(h: var Holder) = fb(h.r.s[0])  # passed to a `var` param
func viaSwap(n: Node) = swap(n.s[0], n.s[1])
func viaResult(n: var Node): var int = n.s[0] # `var T` result behind the ref
var n = Node(s: @[10, 20])
viaInc(n); echo n.s[0], " ", n.s[1]
var h = Holder(r: n)
viaVarArg(h); echo n.s[0], " ", n.s[1]
viaSwap(n); echo n.s[0], " ", n.s[1]
