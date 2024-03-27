import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Util.Quote
import LeanHoG.Util.RBSet
import LeanHoG.Certificate
import Std

open Qq

namespace LeanHoG

def connectedComponentsCertificateOfData (G : Q(Graph)) (C : ConnectedComponentsData) : Q(ConnectedComponentsCertificate $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have val : Q(Nat) := Lean.mkRawNatLit C.val
  have zeroVal : Q(Fin $val) := finOfData val 0
  have zeroVert : Q(Graph.vertex $G) := finOfData n 0
  have convertToPairFinVal : Nat × Nat → Q(Fin $n × Fin $val) := fun (i,j) => q(($(finOfData n i), $(finOfData val j)))
  have componentMap : Q(Std.RBMap (Graph.vertex $G) (Fin $val) Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.component.map convertToPairFinVal) q(Fin.instLinearOrderFin)
  have component : Q(Graph.vertex $G → Fin $val) := q(fun v => Std.RBMap.findD $componentMap v $zeroVal)
  have componentEdge : Q(Std.RBSet.all (Graph.edgeTree $G) (fun x => $component (Graph.fst x) = $component (Graph.snd x)) = true) := (q(Eq.refl true) : Lean.Expr)
  have convertToPairValFin : Nat × Nat → Q(Fin $val × Fin $n) := fun (i,j) => q(($(finOfData val i), $(finOfData n j)))
  have rootMap : Q(Std.RBMap (Fin $val) (Graph.vertex $G) Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.root.map convertToPairValFin) q(Fin.instLinearOrderFin)
  have root : Q(Fin $val → Graph.vertex $G) := q(fun v => Std.RBMap.findD $rootMap v $zeroVert)
  have rootCorrect : Q(forallFin (fun i => $component ($root i) = i) = true) := (q(Eq.refl true) : Lean.Expr)
  have convertToPairOfFins : Nat × Nat → Q(Fin $n × Fin $n) := fun (i,j) => q(($(finOfData n i), $(finOfData n j)))
  have nextMap : Q(Std.RBMap (Graph.vertex $G) (Graph.vertex $G) Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.next.map convertToPairOfFins) q(Fin.instLinearOrderFin)
  have next : Q(Graph.vertex $G → Graph.vertex $G) := q(fun v => Std.RBMap.findD $nextMap v v)
  have convertToFinNat : Nat × Nat → Q(Fin $n × Nat) := fun (i,j) => q(($(finOfData n i), $j))
  have distToRootMap : Q(Std.RBMap (Graph.vertex $G) Nat Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.distToRoot.map convertToFinNat) q(Fin.instLinearOrderFin)
  have distToRoot : Q(Graph.vertex $G → Nat) := q(fun v => Std.RBMap.findD $distToRootMap v 0)
  have distRootZero : Q(forallFin (fun i => $distToRoot ($root i) = 0) = true) := (q(Eq.refl true) : Lean.Expr)
  have distZeroRoot : Q(forallVertex (fun (v : Graph.vertex $G) => $distToRoot v = 0 → v = $root ($component v)) = true) := (q(Eq.refl true) : Lean.Expr)
  have nextRoot : Q(forallFin (fun i => $next ($root i) = $root i) = true) := (q(Eq.refl true) : Lean.Expr)
  have nextAdjacent : Q(decide (∀ (v : Graph.vertex $G), 0 < $distToRoot v → Graph.adjacent v ($next v)) = true) := (q(Eq.refl true) : Lean.Expr)
  have distNext : Q(decide (∀ (v : Graph.vertex $G), 0 < $distToRoot v → $distToRoot ($next v) < $distToRoot v)) := (q(Eq.refl true) : Lean.Expr)
  q(ConnectedComponentsCertificate.mk
         $val
         $component
         $componentEdge
         $root
         (of_decide_eq_true $rootCorrect)
         $next
         $distToRoot
         (of_decide_eq_true $distRootZero)
         (of_decide_eq_true $distZeroRoot)
         (of_decide_eq_true $nextRoot)
         (of_decide_eq_true $nextAdjacent)
         (of_decide_eq_true $distNext)
        )

end LeanHoG
