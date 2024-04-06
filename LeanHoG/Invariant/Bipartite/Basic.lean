import LeanHoG.Graph
import LeanHoG.VertexColoring

namespace LeanHoG

class BipartiteCertificate (G : Graph) extends TwoColoring G where

  /-- A vertex of color 0 -/
  vertex0 : G.vertex

  /-- A vertex of color 1-/
  vertex1 : G.vertex

  /-- Vertex 0 has color 0 -/
  vertex0Color : color vertex0 = 0

  /-- Vertex 1 has color 1 -/
  vertex1Color : color vertex1 = 1

deriving Fintype


/-- A graph is bipartite if there is a 2-coloring of vertices which assigns
    different colors to adjacent vertices. -/
@[simp] def Graph.bipartite (G : Graph) : Prop := ∃ (_ : BipartiteCertificate G), True

instance (G : Graph): Decidable G.bipartite := by
  simp
  infer_instance

/-- A graph is bipartite if it has a bipartite certificate.  -/
@[default_instance]
instance Graph.bipartiteFromCerficate (G : Graph) [B : BipartiteCertificate G] : Decidable G.bipartite
:= by apply isTrue; exists B

class OddClosedWalk (G : Graph) where
  vertex : G.vertex
  walk : ClosedWalk G vertex
  oddLength : Odd walk.length

theorem OddClosedWalk.not_bipartite {G : Graph} (O : OddClosedWalk G) : ¬ Graph.bipartite G := by
  intro bG
  cases bG with
  | intro BG _ =>
    have h := BG.odd_walk O.walk O.oddLength
    contradiction

/-- A graph is not bipartite if it contains an odd closed walk.  -/
@[default_instance]
instance Graph.nonBipartiteFromOddClosedWalk (G : Graph) [W : OddClosedWalk G] : Decidable G.bipartite :=
  .isFalse W.not_bipartite

end LeanHoG
