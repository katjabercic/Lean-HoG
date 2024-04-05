import LeanHoG.Graph

namespace LeanHoG

class BipartiteCertificate (G : Graph) where

  /-- A coloring of vertices by two colors -/
  color : G.vertex → Fin 2

  /-- A vertex of color 0 -/
  vertex0 : G.vertex

  /-- A vertex of color 1-/
  vertex1 : G.vertex

  /-- Neighbors have different colors -/
  edgeColor : ∀ (e : G.edge), color e.val.fst ≠ color e.val.snd

  /-- Vertex 0 has color 0 -/
  vertex0Color : color vertex0 = 0

  /-- Vertex 1 has color 1 -/
  vertex1Color : color vertex1 = 1

/-- A graph is bipartite if there is a 2-coloring of vertices which assigns
    different colors to adjacent vertices. -/
@[reducible]
def Graph.isBipartite (G : Graph) : Prop :=
  ∃ (c : G.vertex → Fin 2), ∃ (v0 v1 : G.vertex), c v0 ≠ c v1 ∧ ∀ (e : G.edge), c e.val.fst ≠ c e.val.snd


/-- A graph is bipartite if it has a Bipartite certificate.  -/
theorem Graph.is_bipartite_if_has_certificate (G : Graph) [B : BipartiteCertificate G] :
  G.isBipartite := by
  use B.color, B.vertex0, B.vertex1
  constructor
  · rw [B.vertex0Color, B.vertex1Color]
    simp
  · exact B.edgeColor

end LeanHoG
