type
  NodeObj = object
    s: seq[int]
  Node = ref NodeObj
func control(n: Node) = n.s[0] = 5
