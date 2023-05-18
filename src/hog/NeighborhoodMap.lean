import TreeSet
import Graph

namespace HoG

class NeighborhoodMap (G : Graph) : Type where
  val : G.vertex → STree G.vertex
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ (val u).mem v

@[reducible, simp]
def Graph.neighborhoodTree (G : Graph) [n : NeighborhoodMap G] (v : G.vertex) := n.val v

lemma Graph.neighborhoodSize (G : Graph) [n : NeighborhoodMap G] (v : G.vertex) :
  G.degree v = (G.neighborhoodTree v).size := by
  unfold degree





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
