import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  A structure that corresponds to the JSON description of bipartiteness certificate.
-/
structure BipartitenessData : Type where

  /-- A coloring of vertices by two colors -/
  color : Array (Nat × Nat)

  /-- A vertex of color 0 -/
  vertex0 : Nat

  /-- A vertex of color 1-/
  vertex1 : Nat
deriving Lean.FromJson


end LeanHoG
