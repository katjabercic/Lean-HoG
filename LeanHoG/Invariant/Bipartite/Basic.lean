import LeanHoG.Graph
import LeanHoG.VertexColoring

namespace LeanHoG

/-- A graph is bipartite if there is a 2-coloring of vertices which assigns
    different colors to adjacent vertices. -/
@[simp] def Graph.bipartite (G : Graph) : Prop := ∃ (_ : TwoColoring G), True

instance (G : Graph): Decidable G.bipartite := by
  simp
  infer_instance

/-- A graph is bipartite if it has a bipartite certificate.  -/
@[default_instance 200]
instance Graph.bipartiteFromTwoColoring (G : Graph) [C : TwoColoring G] : Decidable G.bipartite
:= by apply isTrue; exists C

/-- Having an odd closed walk is an anti-certificate for bipartiteness. -/
class OddClosedWalk (G : Graph) where
  vertex : G.vertex
  walk : ClosedWalk G vertex
  oddLength : Odd walk.length

theorem OddClosedWalk.not_bipartite {G : Graph} (O : OddClosedWalk G) : ¬ Graph.bipartite G := by
  rintro ⟨BG⟩
  have h := BG.odd_walk O.walk O.oddLength
  contradiction

/-- A graph is not bipartite if it contains an odd closed walk.  -/
@[default_instance 200]
instance Graph.nonBipartiteFromOddClosedWalk (G : Graph) [W : OddClosedWalk G] : Decidable G.bipartite :=
  .isFalse W.not_bipartite

end LeanHoG
