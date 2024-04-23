import Std.Data.RBMap
import LeanHoG.Graph
import LeanHoG.Edge
import LeanHoG.Util.RB

namespace LeanHoG

@[reducible]
def edgeCorrect (G : Graph) (M : G.vertexMap G.vertexSubset) :
  G.edgeType → Prop :=
  fun e => (G.fst e) ∈ (M.findD (G.snd e) Std.RBSet.empty) ∧ (G.snd e) ∈ (M.findD (G.fst e) Std.RBSet.empty)

class NeighborhoodMap (G : Graph) where
  neighbors : G.vertexMap G.vertexSubset
  neighbor_is_adjacent : ∀ (u : G.vertex), (neighbors.findD u Std.RBSet.empty).all (G.adjacent u)
  adjacent_is_neighbor : ∀ e : G.edge, edgeCorrect G neighbors e

end LeanHoG
