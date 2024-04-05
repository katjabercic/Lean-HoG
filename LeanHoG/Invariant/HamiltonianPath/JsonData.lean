import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  JSON encoding of a Hamiltonian path.
-/
structure HamiltonianPathData : Type where
  /-- Hamiltonian path -/
  path : List Nat

deriving Lean.FromJson


end LeanHoG
