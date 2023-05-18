import Graph
import NeighborhoodMap

namespace HoG

class DegreeMap (G : Graph) : Type where
  val : G.vertex → Nat
  correct : ∀ (u : G.vertex), val u = G.degree u

-- specialized constructor for JSON decoding
def DegreeMap.mk'
  (G : Graph)
  [N : NeighborhoodMap G]
  (d : G.vertex → Nat)
  (H : (decide (∀ (u : G.vertex), d u = (N.val u).size) = true)) :
  DegreeMap G :=
  { val := d,
    correct := by
      intro u
      apply Eq.trans (b := (N.val u).size)
      · exact (of_decide_eq_true H u)
      · apply Eq.symm ; unfold Graph.degree ; have X := (N.val u).size_is_card
  }

end HoG
