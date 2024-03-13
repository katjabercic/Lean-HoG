import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Connectivity
import LeanHoG.RBSetUtils

namespace LeanHoG

open Qq

/-- Construct a quoted edge from a pair of numbers -/
def edgeOfData (n : Q(Nat)) : Nat × Nat → Q(Edge $n) :=
  fun (a, b) =>
  have H1 : Q(Nat.blt $a $b = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $n = true) := (q(Eq.refl true) : Lean.Expr)
  q(Edge.mk' $n $a $b $H1 $H2)

/-- Construct a quoted element of Fin -/
def finOfData (n : Q(Nat)) (k : Nat) : Q(Fin $n) :=
  have k : Q(Nat) := Lean.mkRawNatLit k
  have H : Q(Nat.blt $k $n = true) := (q(Eq.refl true) : Lean.Expr)
  q(Fin.mk $k (Nat.le_of_ble_eq_true $H))

/-- Construct a quoted graph from graph data -/
def graphOfData (D : GraphData) : Q(Graph) :=
  have vertexSize : Q(Nat) := Lean.mkRawNatLit D.vertexSize
  have arrQ : Array Q(LeanHoG.Edge $vertexSize) := D.edges.map (LeanHoG.edgeOfData vertexSize)
  have edges : Q(Std.RBSet (LeanHoG.Edge $vertexSize) LeanHoG.Edge.linearOrder.compare) := build_RBSet arrQ q(LeanHoG.Edge.linearOrder)
  q(Graph.mk $vertexSize $edges)

/-- Construct a connectivity certificate from connectivity data -/
def connectivityCertificateOfData (G : Q(Graph)) (C : ConnectivityData) : Q(ConnectivityCertificate $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have root : Q(Graph.vertex $G) := finOfData n C.root
  have convertToPairOfFins : Nat × Nat → Q(Fin $n × Fin $n) := fun (i,j) => q(($(finOfData n i), $(finOfData n j)))
  have nextMap : Q(Std.RBMap (Graph.vertex $G) (Graph.vertex $G) Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.next.map convertToPairOfFins) q(Fin.instLinearOrderFin)
  have next : Q(Graph.vertex $G → Graph.vertex $G) := q(fun v => Std.RBMap.findD $nextMap v v)
  have convertToFinNat : Nat × Nat → Q(Fin $n × Nat) := fun (i,j) => q(($(finOfData n i), $j))
  have distToRootMap : Q(Std.RBMap (Graph.vertex $G) Nat Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.distToRoot.map convertToFinNat) q(Fin.instLinearOrderFin)
  have distToRoot : Q(Graph.vertex $G → Nat) := q(fun v => Std.RBMap.findD $distToRootMap v 0)
  have nextAdjacent : Q(decide (∀ (v : Graph.vertex $G), v ≠ $root → Graph.adjacent v ($next v)) = true) := (q(Eq.refl true) : Lean.Expr)
  have distNext : Q(decide (∀ (v : Graph.vertex $G), v ≠ $root → $distToRoot ($next v) < $distToRoot v)) := (q(Eq.refl true) : Lean.Expr)
  q(ConnectivityCertificate.mk
    $root
    $next
    $distToRoot
    (of_decide_eq_true $nextAdjacent)
    (of_decide_eq_true $distNext))

/-- Construct a disconnectivity certificate from connectivity data -/
def disconnectivityCertificateOfData (G : Q(Graph)) (D : DisconnectivityData) : Q(DisconnectivityCertificate $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have convertToFin : Nat × Nat → Q(Fin $n × Fin 2) := fun (i,j) => q(($(finOfData n i), $(finOfData (Lean.mkRawNatLit 2) j)))
  have colorMap : Q(Std.RBMap (Graph.vertex $G) (Fin 2) Fin.instLinearOrderFin.compare) :=
    build_RBMap (D.color.map convertToFin) q(Fin.instLinearOrderFin)
  have color : Q(Graph.vertex $G → Fin 2) := q(fun v => Std.RBMap.findD $colorMap v 0)
  have vertex0 : Q(Graph.vertex $G) := finOfData n D.vertex0
  have vertex1 : Q(Graph.vertex $G) := finOfData n D.vertex1
  have edgeColor : Q(Std.RBSet.all (Graph.edgeTree $G) (fun e => $color e.fst = $color e.snd) = true) := (q(Eq.refl true) : Lean.Expr)
  have vertex0Color : Q($color $vertex0 = 0) := (q(Eq.refl (0 : Fin 2)) : Lean.Expr)
  have vertex1Color : Q($color $vertex1 = 1) := (q(Eq.refl (1 : Fin 2)) : Lean.Expr)
  q(DisconnectivityCertificate.mk
    $color
    $vertex0
    $vertex1
    (Graph.all_edges $G (fun e => $color e.fst = $color e.snd) $edgeColor)
    $vertex0Color
    $vertex1Color
  )

end LeanHoG
