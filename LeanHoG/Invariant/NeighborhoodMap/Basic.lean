import Std.Data.RBMap

import LeanHoG.Graph
import LeanHoG.Edge
import LeanHoG.Util.RBSet

namespace LeanHoG

class NeighborhoodMap (G : Graph) where
  neighbors : Std.RBMap G.vertex (Std.RBSet G.vertex G.vertex_compare) G.vertex_compare
  neighbor_is_adjacent : ∀ (u : G.vertex), (neighbors.find! u).all (G.adjacent u)
  adjacent_is_neighbor : ∀ e : G.edge, (e.val.fst ∈ neighbors.find! e.val.snd) ∧ (e.val.snd ∈ neighbors.find! e.val.fst)

end LeanHoG
