import Lake
open Lake DSL

package «LeanHoG» {
  srcDir := "src"
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib HoG where
  -- the default setting of autoImplicit=true is insane

lean_lib BoundedOrder
lean_lib OrdEq
lean_lib TreeSet
lean_lib TreeMap
lean_lib Edge
lean_lib Graph
-- lean_lib Test
-- lean_lib OneGraph
-- lean_lib Query
-- lean_lib Tactic
lean_lib Invariant.EdgeSize
lean_lib Invariant.NeighborhoodMap
lean_lib Invariant.DegreeMap
lean_lib Invariant.ConnectedComponents
lean_lib JsonDecoder
-- lean_lib Walk
-- lean_lib Bipartite
