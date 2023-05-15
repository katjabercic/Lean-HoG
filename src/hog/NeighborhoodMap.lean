import TreeSet
import Graph

namespace HoG

class NeighborhoodMap (G : Graph) (α : Type) [mem : Membership G.vertex α] : Type where
  val : G.vertex → α
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ v ∈ val u

-- specialized constructor for JSON decoding
def NeighborhoodMap.mk' (G : Graph) (m : G.vertex → STree G.vertex) (H : (decide (∀ (u v : G.vertex), G.adjacent u v ↔ (m u).mem v) = true)) :
  NeighborhoodMap G (STree G.vertex) :=
  { val := m,
    correct := by simp_all
  }

end HoG
