import TreeSet
import Graph

namespace HoG

class NeighborhoodMap (G : Graph) : Type where
  val : G.vertex → STree G.vertex
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ (val u).mem v

@[reducible, simp]
def Graph.neighborhoodTree (G : Graph) [n : NeighborhoodMap G] (v : G.vertex) := n.val v

lemma NeighborhoodMap.neighborhoodSize (G : Graph) [n : NeighborhoodMap G] (v : G.vertex) :
  G.degree v = (G.neighborhoodTree v).size := by
  apply Eq.trans (b := Fintype.card (n.val v).set)
  · apply Fintype.card_congr
    apply (Equiv.subtypeEquiv (Equiv.refl G.vertex))
    intro u
    exact (n.correct v u)
  · apply STree.size_is_card

-- specialized constructor for JSON decoding
def NeighborhoodMap.mk'
  (G : Graph)
  (m : G.vertex → STree G.vertex)
  (H : (decide (∀ (u v : G.vertex), G.adjacent u v ↔ (m u).mem v) = true)) :
  NeighborhoodMap G :=
  { val := m,
    correct := by simp_all
  }

end HoG