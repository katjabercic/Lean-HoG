import Qq
import LeanHoG.Graph
import LeanHoG.Util.RBSet
import LeanHoG.Invariant.NeighborhoodMap.Basic
import LeanHoG.Invariant.NeighborhoodMap.JsonData


namespace LeanHoG

open Qq

def neighborhoodMapOfData (G : Q(Graph)) (M : NeighborhoodMapData) : Q(NeighborhoodMap $G) :=
  have nbhMap : Q(Std.RBMap (Graph.vertex $G) (Std.RBSet (Graph.vertex $G) Graph.vertex_compare) Graph.vertex_compare) :=
    build_RBMap
  q(NeighborhoodMap.mk
    $nbhMap
    $nbhEdge
    $edgeNbh
  )


end LeanHoG
