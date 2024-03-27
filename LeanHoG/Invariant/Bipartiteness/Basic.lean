import LeanHoG.Graph
import LeanHoG.VertexColoring

namespace LeanHoG

class BipartitenessCertificate (G : Graph) where

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


@[simp] def Graph.isBipartite (G : Graph) : Prop :=
  ∃ (c : G.vertex → Fin 2), ∃ (v0 v1 : G.vertex), c v0 ≠ c v1 ∧ ∀ (e : G.edge), c e.val.fst ≠ c e.val.snd


/-- A graph is bipartite if it has a bipartiteness certificate.  -/
theorem Graph.is_bipartite_if_has_certificate (G : Graph) [B : BipartitenessCertificate G] :
  G.isBipartite := by
  use B.color, B.vertex0, B.vertex1
  constructor
  · rw [B.vertex0Color, B.vertex1Color]
    simp
  · exact B.edgeColor


/-
theorem OddClosedWalkNotBipartite
  {G : Graph}
  (v : G.vertex)
  (w : ClosedWalk G v) :
  Odd w.length → ¬ Graph.isBipartite G := by
  intros isOdd p
  cases p with
  | intro c H =>
    apply Exists.elim H
    intro a
    intro H
    apply Exists.elim H
    intro b
    intro H
    obtain ⟨neq_col_a_b, diff_color_edges⟩ := H
    let c_bool : G.vertex → Bool := fun u =>
      match c u with
      | 0 => false
      | 1 => true
    have c_bool_inj (u v : G.vertex) : c u ≠ c v → c_bool u ≠ c_bool v := by
      intro ne_cu_cv
      unfold_let c_bool
      apply ltByCases
    have diff_color_edges_bool : ∀ (e : G.edge), c_bool e.val.fst ≠ c_bool e.val.snd := by
      intro e
      simp
      sorry
    sorry
    --let _ := (VertexColoring.EvenOddWalkEndpointEquality w c).left isOdd
    --contradiction
-/

end LeanHoG
