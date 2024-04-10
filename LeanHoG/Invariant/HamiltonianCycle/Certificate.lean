import Qq
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote
import LeanHoG.Invariant.HamiltonianCycle.Basic
import LeanHoG.Invariant.HamiltonianCycle.JsonData

namespace LeanHoG

open Qq
def hamiltonianCycleOfData (G : Q(Graph)) (D : HamiltonianCycleData) : Q(HamiltonianCycle $G) :=
  -- Helper function to compute a Walk from a list of vertices
  let rec fold (t : Q(Graph.vertex $G)) : List Q(Graph.vertex $G) →
    ((s : Q(Graph.vertex $G)) ×' Q(Walk $G $s $t)) := fun vs =>
    match vs with
    | [] => panic! "given empty path, cannot construct Hamiltonian cycle"
    | [v] =>
      let h : Q($v = $t) := (q(Eq.refl $v) : Lean.Expr)
      ⟨v, q($h ▸ .here $v)⟩
    | u :: v :: vs =>
      let ⟨s, w⟩ := fold t (v :: vs)
      let h : Q(decide (@Graph.adjacent $G $u $s) = true) := (q(Eq.refl true) : Lean.Expr)
      let w' := q(.step (of_decide_eq_true $h) $w)
      ⟨u, w'⟩

  have n : Q(Nat) := q(Graph.vertexSize $G)
  let vertices : List Q(Graph.vertex $G) := D.cycle.map (finOfData n)
  -- Construct the Hamiltonian cycle from the path
  match vertices.getLast? with
  | none => panic! "no vertices"
  | some t =>
    let ⟨s, w⟩ : ((s : Q(Graph.vertex $G)) ×' Q(Walk $G $s $t)) := fold t vertices
    -- Check that w starts and end in the same vertex
    let isClosed : Q($s = $t) := (q(Eq.refl true) : Lean.Expr)
    -- Declare w to actually be a closed walk, we know this from above
    let cw : Q(ClosedWalk $G $s) := w
    -- Check that it is a cycle, i.e. no repeating vertices
    sorry
    -- let isCycle : Q(decide (ClosedWalk.isCycle $cw) = true) := (q(Eq.refl true) : Lean.Expr)
    -- let c : Q(Cycle $G $s) := q(@Cycle.mk $G $s $cw (of_decide_eq_true $isCycle))
    -- let isHamiltonian : Q(decide (Cycle.isHamiltonian $c) = true) := (q(Eq.refl true) : Lean.Expr)
    -- let hc : Q(HamiltonianCycle $G) :=
    --   q(@HamiltonianCycle.mk $G $s (Cycle.mk $cw (of_decide_eq_true (_))) (of_decide_eq_true $isHamiltonian))
    -- hc
