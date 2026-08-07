import LeanHoG.Graph
import LeanHoG.VertexColoring

namespace LeanHoG

/-- A graph is bipartite if there is a 2-coloring of vertices which assigns
    different colors to adjacent vertices. -/
@[simp] def Graph.bipartite (G : Graph) : Prop := ∃ (_ : TwoColoring G), True

/-- The maps `G.vertex → Fin 2` that give adjacent vertices different colors. -/
def Graph.properTwoColorings (G : Graph) : Finset (G.vertex → Fin 2) :=
  Finset.univ.filter (fun c => ∀ u v : G.vertex, G.adjacent u v → c u ≠ c v)

theorem Graph.mem_properTwoColorings {G : Graph} {c : G.vertex → Fin 2} :
    c ∈ G.properTwoColorings ↔ isVertexColoring G c := by
  simp only [Graph.properTwoColorings, Finset.mem_filter, Finset.mem_univ, true_and,
    isVertexColoring]

theorem Graph.bipartite_iff_properTwoColorings_nonempty (G : Graph) :
    G.bipartite ↔ G.properTwoColorings.Nonempty := by
  constructor
  · rintro ⟨C, -⟩
    exact ⟨C.color, G.mem_properTwoColorings.mpr C.isColoring⟩
  · rintro ⟨c, hc⟩
    exact ⟨@TwoColoring.mk G ⟨c, G.mem_properTwoColorings.mp hc⟩, trivial⟩

instance (G : Graph) : Decidable G.bipartite :=
  decidable_of_iff _ (G.bipartite_iff_properTwoColorings_nonempty).symm

/-- A graph is bipartite if it has a bipartite certificate.  -/
@[default_instance]
instance Graph.bipartiteFromTwoColoring (G : Graph) [C : TwoColoring G] : Decidable G.bipartite
:= by apply isTrue; exists C

/-- A two-coloring is a certificate for bipartiteness. -/
theorem TwoColoring.bipartite {G : Graph} (C : TwoColoring G) : Graph.bipartite G := ⟨C, trivial⟩

/-- Having an odd closed walk is an anti-certificate for bipartiteness. -/
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
