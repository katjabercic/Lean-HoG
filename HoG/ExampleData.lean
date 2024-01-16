import HoG.Graph
import HoG.Invariant.EdgeSize
import HoG.Invariant.Hamiltonian.SatEncoding
import LeanSAT

namespace HoG

open LeanSAT

def piglet1 : Graph :=
  { vertexSize := 3,
    edgeTree := .node (Edge.mk 2 ⟨0, by simp⟩) (.leaf (Edge.mk 1 ⟨0, by simp⟩)) (.leaf (Edge.mk 2 ⟨1, by simp⟩)) }

instance : EdgeSize piglet1 where
  val := 3
  correct := by rfl

instance : Solver IO := Solver.Impl.DimacsCommand "/home/jure/source-control/kissat/build/kissat"

#eval (findHamiltonianCycle piglet1)

end HoG
