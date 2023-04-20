import Lake
open Lake DSL

package «lean-HOG» {
  srcDir := "src/hog"
}

@[default_target]
lean_lib HoG where

lean_lib BoundedOrder
lean_lib TreeSet
lean_lib TreeMap
lean_lib Graph
lean_lib EdgeSize
lean_lib GraphJson
lean_lib OneGraph
-- lean_lib Query
-- lean_lib NeighborMap
-- lean_lib Tactic
-- lean_lib ConnectedComponents
-- lean_lib Walk
-- lean_lib Bipartite
lean_lib Data {
  srcDir := "data"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
