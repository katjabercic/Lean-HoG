import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  The JSON encoding of a neighborhood map is represented by an array
  of pairs (u, vs) where u is a vertex and vs is an array representing
  the set of u's neighbors. As always, the array must be ordered by
  u's, and each vs must be ordered as well.
-/
structure NeighborhoodMapData : Type where
  neighbors : Array (Nat × Array Nat)

deriving Lean.FromJson

end LeanHoG
