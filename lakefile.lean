import Lake
open Lake DSL

package «LeanHoG» {
  srcDir := "src/hog"
}

@[default_target]
lean_lib HoG where

-- the default setting of autoImplicit is insane
moreLeanArgs := #["-DautoImplicit=false"]

lean_lib BoundedOrder
lean_lib OrdEq
lean_lib TreeSet
lean_lib TreeMap
lean_lib Edge
lean_lib Graph
lean_lib EdgeSize
lean_lib JsonDecoder
-- lean_lib OneGraph
-- lean_lib Query
-- lean_lib NeighborMap
-- lean_lib Tactic
lean_lib ConnectedComponents
-- lean_lib Walk
-- lean_lib Bipartite

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
