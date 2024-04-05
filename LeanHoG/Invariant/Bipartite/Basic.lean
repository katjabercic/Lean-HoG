import LeanHoG.Graph
import LeanHoG.VertexColoring

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
@[simp] def Graph.bipartite (G : Graph) : Prop :=
  ∃ (c : G.vertex → Fin 2), ∃ (v0 v1 : G.vertex), c v0 ≠ c v1 ∧ ∀ (e : G.edge), c e.val.fst ≠ c e.val.snd

instance (G : Graph): Decidable (Graph.bipartite G) := by
  simp
  infer_instance

/-- A graph is bipartite if it has a bipartite certificate.  -/
@[default_instance]
instance Graph.bipartiteFromCerficate (G : Graph) [B : BipartiteCertificate G] : Decidable G.bipartite
:= by
  apply isTrue
  use B.color, B.vertex0, B.vertex1
  constructor
  · rw [B.vertex0Color, B.vertex1Color]
    simp
  · exact B.edgeColor


theorem OddClosedWalkNotBipartite
  {G : Graph}
  (v : G.vertex)
  (w : ClosedWalk G v) :
  Odd w.length → ¬ Graph.bipartite G := by
  intros isOdd p
  cases p with
  | intro c H =>
    apply Exists.elim H
    intro a
    intro H
    apply Exists.elim H
    intro b
    intro H
    obtain ⟨_, diff_color_edges⟩ := H
    have coloring : VertexColoring (Fin 2) G := {
      color := c,
      colorCorrect := diff_color_edges
    }
    let _ := (VertexColoring.EvenOddWalkEndpointEquality w coloring).left isOdd
    contradiction

class OddClosedWalk (G : Graph) where
  vertex : G.vertex
  walk : ClosedWalk G vertex
  oddLength : Odd walk.length

/-- A graph is not bipartite if it contains an odd closed walk.  -/
@[default_instance]
instance Graph.nonBipartiteFromOddClosedWalk (G : Graph) [W : OddClosedWalk G] : Decidable G.bipartite :=
  .isFalse (OddClosedWalkNotBipartite W.vertex W.walk W.oddLength)

end LeanHoG
