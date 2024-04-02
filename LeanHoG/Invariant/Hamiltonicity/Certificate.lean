import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote

namespace LeanHoG

open Qq
def hamiltonianPathOfData (G : Q(Graph)) (D : PathData) : Q(HamiltonianPath $G) :=
  let rec fold (t : Q(Graph.vertex $G)) :
    List Q(Graph.vertex $G) → ((s : Q(Graph.vertex $G)) ×' Q(Walk $G $s $t)) := fun vs =>
    match vs with
    | [] => panic! "Shouldn't be here"
    | [v] =>
      let h : Q($v = $t) := (q(Eq.refl $v) : Lean.Expr)
      ⟨v, q($h ▸ Walk.trivial $v)⟩
    | u :: v :: vs =>
      let ⟨s, w⟩ := fold t (v :: vs)
      let h : Q(decide (@Graph.adjacent $G $u $s) = true) := (q(Eq.refl true) : Lean.Expr)
      let w' := q(Walk.left (of_decide_eq_true $h) $w)
      ⟨u, w'⟩
  have n : Q(Nat) := q(Graph.vertexSize $G)
  let vertices : List Q(Graph.vertex $G) := D.vertices.map (finOfData n)
  match vertices.getLast? with
  | none => panic! "no vertices"
  | some t =>
    let ⟨s, w⟩ := fold t vertices
    let isPath : Q(decide (@Walk.isPath $G $s $t $w) = true) := (q(Eq.refl true) : Lean.Expr)
    let p : Q(Path $G $s $t) := q(@Path.mk $G $s $t $w (of_decide_eq_true $isPath))
    let isHamiltonian : Q(decide (Path.isHamiltonian $p) = true) := (q(Eq.refl true) : Lean.Expr)
    let hp : Q(HamiltonianPath $G) := q(@HamiltonianPath.mk $G $s $t (Path.mk $w (of_decide_eq_true $isPath)) (of_decide_eq_true $isHamiltonian))
    hp
