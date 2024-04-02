import Qq
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote
import LeanHoG.Invariant.NeighborhoodMap.Basic
import LeanHoG.Invariant.NeighborhoodMap.JsonData


namespace LeanHoG

open Qq

#check finOfData

def finSetOfData (n : Q(Nat)) (a : Array Nat) : Q(Std.RBSet (Fin $n) Fin.instLinearOrderFin.compare) :=
  build_RBSet (a.map (finOfData n)) q(Fin.instLinearOrderFin)

def neighborhoodMapOfData (G : Q(Graph)) (M : NeighborhoodMapData) : Q(NeighborhoodMap $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have convert : Nat × Array Nat → Q(Fin $n × Std.RBSet (Fin $n) Fin.instLinearOrderFin.compare) :=
    fun (u, vs) => q(($(finOfData n u), $(finSetOfData n vs)))
  have nbhMap : Q(Std.RBMap (Graph.vertex $G) (Std.RBSet (Graph.vertex $G) Graph.vertex_compare) Graph.vertex_compare) :=
    build_RBMap (M.neighbors.map convert) q(Fin.instLinearOrderFin)
  have nbhAdj : Q(decide (∀ (u : Graph.vertex $G), ($(nbhMap).find! u).all (@Graph.adjacent $G u)) = true) :=
    (q(Eq.refl true) : Lean.Expr)
  have adjNbh : Q(Std.RBSet.all (Graph.edgeTree $G) (edgeCorrect $G $nbhMap) = true) := (q(Eq.refl true) : Lean.Expr)
  q(NeighborhoodMap.mk
    $nbhMap
    (of_decide_eq_true $nbhAdj)
    (Graph.all_edges $G (edgeCorrect $G $nbhMap) $adjNbh)
  )

end LeanHoG
