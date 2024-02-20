import LeanHoG.Graph
import LeanHoG.Widgets
import LeanHoG.Invariants.Hamiltonicity.SatEncoding
import LeanSAT

namespace LeanHoG

open LeanSAT

def no_ham : Graph :=
  {
    vertexSize := 3,
    edgeTree :=
      .node (Edge.mk 1 ⟨2, by norm_num⟩ (by norm_num))
        (.leaf (Edge.mk 0 ⟨1, by norm_num⟩ (by norm_num)))
        .empty
    edgeCorrect := by rfl
  }

instance : Solver IO := Solver.Impl.DimacsCommand "kissat"

#eval showNoHamiltonianPath no_ham

#visualizeHamiltonianPath? no_ham


























abbrev g1 : Graph :=
  {
    vertexSize := 2,
    edgeTree :=
      .node (Edge.mk 0 ⟨1, by norm_num⟩ (by norm_num))
        (.empty)
        (.empty)
    edgeCorrect := by rfl
  }

#widget visualize with g1.toVisualizationFormat

def w : Walk g1 0 1 :=
  .left (by decide) (.trivial 1)

def p : Path g1 0 1 := {
  walk := w
}
instance : HamiltonianPath g1 where
  u := 0
  v := 1
  path := p

#visualizeHamiltonianPath g1



end LeanHoG
