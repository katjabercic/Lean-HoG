import HoG.Graph
import HoG.Invariant.EdgeSize
import HoG.Invariant.Hamiltonian.SatEncoding
import LeanSAT

namespace HoG

open LeanSAT Model

def piglet1 : Graph :=
  { vertexSize := 3,
    edgeTree :=
      .node (Edge.mk 0 ⟨2, by simp⟩ (by norm_num))
        (.leaf (Edge.mk 0 ⟨1, by simp⟩ (by norm_num)))
        (.leaf (Edge.mk 1 ⟨2, by simp⟩ (by norm_num)))
    edgeCorrect := by rfl
  }

instance : EdgeSize piglet1 where
  val := 3
  correct := by rfl

instance : Solver IO := Solver.Impl.DimacsCommand "kissat"

-- #eval (findHamiltonianCycle piglet1)

--======================================
-- Example without a Hamiltonian path
-- A star configuration on 4 vertices
--======================================

def no_ham : Graph :=
  {
    vertexSize := 4,
    edgeTree :=
      .node (Edge.mk 1 ⟨2, by norm_num⟩ (by norm_num))
        (.leaf (Edge.mk 0 ⟨1, by norm_num⟩ (by norm_num)))
        (.leaf (Edge.mk 1 ⟨3, by norm_num⟩ (by norm_num)))
    edgeCorrect := by rfl
  }

#eval showNoHamiltonianPath no_ham


--======================================
-- Smaller example, path with 2 vertices
--======================================

-- def piglet0 : Graph :=
--   { vertexSize := 2,
--     edgeTree := .node (Edge.mk 1 ⟨0, by simp⟩) .empty .empty }

-- #eval (findHamiltonianCycle piglet0)

end HoG
