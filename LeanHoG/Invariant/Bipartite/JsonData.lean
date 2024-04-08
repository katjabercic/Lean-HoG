import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  JSON encoding of a two-coloring.
-/
structure TwoColoringData : Type where

  /-- A coloring of vertices by two colors -/
  color : Array (Nat × Nat)

deriving Lean.FromJson

/--
  JSON encoding of an odd closed walk -/
structure OddClosedWalkData : Type where

  closedWalk : List Nat

deriving Lean.FromJson

end LeanHoG
