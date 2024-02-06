import Qq
import JSON2Lean.JsonData
import JSON2Lean.SetTree
import JSON2Lean.Edge
import JSON2Lean.Graph
import JSON2Lean.Connectivity

namespace JSON2Lean

open Qq

/--
  Given a subarray of values, generate the corresponding balanced search tree.
  NB: The subarray must be sorted by keys.
-/
partial def setTreeOfSubarray {α : Q(Type)} (arr : Array Q($α)) (low high : Nat) : Q(SetTree $α) :=
  if ltSize : low < arr.size ∧ high <= arr.size then
    if _ : low >= high then
      q(.empty)
    else if low + 1 = high then
      let x := arr[low]'(ltSize.1)
      q(.leaf $x)
    else
      let middle := (low + high).div2
      let left :=  setTreeOfSubarray arr low middle
      let right := setTreeOfSubarray arr (middle + 1) high
      have middle_valid : (low + high).div2 < arr.size := (by
        rw [Nat.div2_val]
        have h : (low + high < arr.size + arr.size) → ((low + high) / 2 < arr.size) := (by
          intro ab_lt_nn
          rw [←Nat.two_mul] at ab_lt_nn
          apply Nat.div_lt_of_lt_mul ab_lt_nn)
        apply h
        apply Nat.lt_of_le_of_lt (Nat.add_le_add_left ltSize.2 low) (Nat.add_lt_add_right ltSize.1 arr.size))
      let x := arr[middle]'middle_valid
      q(.node $x $left $right)
  else
    q(.empty)

/--
  Given an array of values, generate the corresponding balanced search tree.
  NB: The array must be sorted by keys.
-/
def setTreeOfArray {α : Q(Type)} (arr : Array Q($α)) : Q(SetTree $α) :=
  setTreeOfSubarray arr 0 arr.size

/--
  Given a subarray of key-value pairs, generate the corresponding balanced map tree.
  NB: The subarray must be sorted by keys.
-/
partial def mapTreeOfSubarray {α β : Q(Type)} (arr : Array (Q($α) × Q($β))) (low high : Nat) : Q(MapTree $α $β) :=
  if ltSize : low < arr.size ∧ high <= arr.size then
    if _ : low >= high then
      q(.empty)
    else if low + 1 = high then
      let (x, y) := arr[low]'(ltSize.1)
      q(.leaf $x $y)
    else
      let middle := (low + high).div2
      let left :=  mapTreeOfSubarray arr low middle
      let right := mapTreeOfSubarray arr (middle + 1) high
      have middle_valid : (low + high).div2 < arr.size := (by
        rw [Nat.div2_val]
        have h : (low + high < arr.size + arr.size) → ((low + high) / 2 < arr.size) := (by
          intro ab_lt_nn
          rw [←Nat.two_mul] at ab_lt_nn
          apply Nat.div_lt_of_lt_mul ab_lt_nn)
        apply h
        apply Nat.lt_of_le_of_lt (Nat.add_le_add_left ltSize.2 low) (Nat.add_lt_add_right ltSize.1 arr.size))
      let (x, y) := arr[middle]'middle_valid
      q(.node $x $y $left $right)
  else
    q(.empty)

/--
  Given an array of key-value pairs, generate the corresponding balanced search tree.
  NB: The array must be sorted by keys.
-/
def mapTreeOfArray {α β : Q(Type)} (arr : Array (Q($α) × Q($β))) : Q(MapTree $α $β) :=
  mapTreeOfSubarray arr 0 arr.size

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
  have edges : Q(SetTree (Edge $vertexSize)) := setTreeOfArray (D.edges.map (edgeOfData vertexSize))
  have edgeCorrect : Q(SetTree.isCorrect $(edges) = true) := (q(Eq.refl true) : Lean.Expr)
  q(Graph.mk $vertexSize $edges $edgeCorrect)

/-- Construct a connectivity certificate from connectivity data -/
def connectivityCertificateOfData (G : Q(Graph)) (C : ConnectivityData) : Q(ConnectivityCertificate $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have root : Q(Graph.vertex $G) := finOfData n C.root
  have nextMap : Q(MapTree (Graph.vertex $G) (Graph.vertex $G)) :=
    mapTreeOfArray (C.next.map (fun (i,j) => (finOfData n i, finOfData n j)))
  have next : Q(Graph.vertex $G → Graph.vertex $G) := q(fun v => MapTree.getD $nextMap v v)
  have distToRootMap : Q(MapTree (Graph.vertex $G) Nat) :=
    mapTreeOfArray (C.distToRoot.map (fun (i,j) => (finOfData n i, Lean.mkRawNatLit j)))
  have distToRoot : Q(Graph.vertex $G → Nat) := q(fun v => MapTree.getD $distToRootMap 0 v)
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
  have colorMap : Q(MapTree (Graph.vertex $G) (Fin 2)) :=
    mapTreeOfArray (D.color.map (fun (i,j) => (finOfData n i, finOfData (Lean.mkRawNatLit 2) j)))
  have color : Q(Graph.vertex $G → Fin 2) := q(fun v => MapTree.getD $colorMap 0 v)
  have vertex0 : Q(Graph.vertex $G) := finOfData n D.vertex0
  have vertex1 : Q(Graph.vertex $G) := finOfData n D.vertex1
  have edgeColor : Q(SetTree.all (Graph.edgeTree $G) (fun e => $color e.fst = $color e.snd) = true) := (q(Eq.refl true) : Lean.Expr)
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

end JSON2Lean
