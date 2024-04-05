import Lean
import LeanHoG.Graph

namespace LeanHoG

/--
  JSON representation of connected components certificate.
-/
structure ConnectedComponentsData : Type where
  /-- The number of connected components. -/
  val : Nat

  /--
  For each vertex, the number of its connected component.
  -/
  component : Array (Nat × Nat)

  /-- The roots of the spanning tree for each component. -/
  root : Array (Nat × Nat)

  /--
  For each vertex that is not a root, the next step of the path leading to the
  root (and the root maps to itself).
  -/
  next : Array (Nat × Nat)

  /--
  To ensure that next is cycle-free, we witness the fact that "next" takes us closer to the root.
  the distance of a vertex to its component root
  -/
  distToRoot : Array (Nat × Nat)

deriving Lean.FromJson


end LeanHoG
