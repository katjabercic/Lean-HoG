import Graph

namespace HoG

class NeighborhoodMap {α : Type} (G : Graph) [Membership G.vertex α] : Type where
  val : G.vertex → α
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ u ∈ val v
end HoG
