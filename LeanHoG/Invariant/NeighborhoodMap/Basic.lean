import Std.Data.RBMap
import LeanHoG.Graph
import LeanHoG.Edge
import LeanHoG.Util.RB

namespace LeanHoG

@[reducible]
def edgeCorrect (G : Graph) (M : Std.RBMap G.vertex (Std.RBSet G.vertex G.vertex_compare) G.vertex_compare) :
  G.edgeType → Prop :=
  fun e => (G.fst e) ∈ (M.findD (G.snd e) Std.RBSet.empty) ∧ (G.snd e) ∈ (M.findD (G.fst e) Std.RBSet.empty)

class NeighborhoodMap (G : Graph) where
  neighbors : Std.RBMap G.vertex (Std.RBSet G.vertex G.vertex_compare) G.vertex_compare
  neighbor_is_adjacent : ∀ (u : G.vertex), (neighbors.findD u Std.RBSet.empty).all (G.adjacent u)
  adjacent_is_neighbor : ∀ e : G.edge, edgeCorrect G neighbors e

end LeanHoG
