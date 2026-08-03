import Qq
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote
import LeanHoG.Invariant.NeighborhoodMap.Basic
import LeanHoG.Invariant.NeighborhoodMap.JsonData


namespace LeanHoG

open Qq

def neighborhoodMapOfData (G : Q(Graph)) (M : NeighborhoodMapData) : Q(NeighborhoodMap $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have vertexSubsetOfData (G : Q(Graph)) (a : Array Nat) : Q(Graph.vertexSubset $G) :=
    build_RBSet (a.map (finOfData q(Graph.vertexSize $G))) q(Fin.instLinearOrder)
  have convert : Nat × Array Nat → Q(Fin $n × Graph.vertexSubset $G) :=
    fun (u, vs) => q(($(finOfData n u), $(vertexSubsetOfData G vs)))
  have nbhMap : Q(Graph.vertexMap $G (Graph.vertexSubset $G)) :=
    build_RBMap (M.neighbors.map convert) q(Fin.instLinearOrder)
  have nbhAdj : Q(decide (∀ (u : Graph.vertex $G), ($(nbhMap).find! u).all (@Graph.adjacent $G u)) = true) :=
    (q(Eq.refl true) : Lean.Expr)
  have adjNbh : Q(Batteries.RBSet.all (Graph.edgeSet $G) (edgeCorrect $G $nbhMap) = true) := (q(Eq.refl true) : Lean.Expr)
  q(NeighborhoodMap.mk
    $nbhMap
    (of_decide_eq_true $nbhAdj)
    (Graph.all_edges $G (edgeCorrect $G $nbhMap) $adjNbh)
  )

end LeanHoG
