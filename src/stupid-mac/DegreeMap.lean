import Graph
import Invariant.NeighborhoodMap

namespace HoG

class DegreeMap (G : Graph) : Type where
  val : G.vertex → Nat
  correct : ∀ (u : G.vertex), val u = G.degree u

instance {G : Graph} : CoeFun (DegreeMap G) (fun _ => G.vertex → Nat) where
  coe := @DegreeMap.val G

-- specialized constructor for JSON decoding
def DegreeMap.mk'
  (G : Graph)
  (nbh : NeighborhoodMap G)
  (d : G.vertex → Nat)
  (H : ∀ (u : G.vertex), d u = (nbh u).size) :
  DegreeMap G :=
  { val := d,
    correct := by
      intro u
      apply Eq.trans (b := (nbh u).size)
      · exact (H u)
      · apply Eq.symm ; apply nbh.neighborhoodSize
  }

end HoG
