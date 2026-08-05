import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  JSON encoding of a Hamiltonian path.
-/
structure HamiltonianCycleData : Type where
  /-- Hamiltonian cycle -/
  cycle : List Nat

deriving Lean.FromJson


end LeanHoG
