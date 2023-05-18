import TreeSet
import Graph

namespace HoG

class NeighborhoodMap (G : Graph) : Type where
  val : G.vertex → STree G.vertex
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ (val u).mem v

instance (G : Graph) : CoeFun (NeighborhoodMap G) (fun _ => G.vertex → STree G.vertex) where
  coe := @NeighborhoodMap.val G

lemma NeighborhoodMap.neighborhoodSize (G : Graph) [nbh : NeighborhoodMap G] (v : G.vertex) :
  G.degree v = (nbh v).size := by
  apply Eq.trans (b := Fintype.card (nbh v).set)
  · apply Fintype.card_congr
    apply (Equiv.subtypeEquiv (Equiv.refl G.vertex))
    intro u
    exact (nbh.correct v u)
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