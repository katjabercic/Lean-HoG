import Qq
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote
import LeanHoG.Certificate
import LeanHoG.Invariant.HamiltonianCycle.Basic
import LeanHoG.Invariant.HamiltonianCycle.JsonData

namespace LeanHoG

open Qq
def hamiltonianCycleOfData (G : Q(Graph)) (D : HamiltonianCycleData) : Q(HamiltonianCycle $G) :=
  -- Helper function to compute a Walk from a list of vertices
  have n : Q(Nat) := q(Graph.vertexSize $G)
  let vertices : List Q(Graph.vertex $G) := D.cycle.map (finOfData n)
  -- Construct the Hamiltonian cycle from the path
  match vertices.getLast? with
  | none => panic! "no vertices"
  | some t =>
    let ⟨s, w⟩ : ((s : Q(Graph.vertex $G)) ×' Q(Walk $G $s $t)) := walkOfVertexList G t vertices
    -- Check that w starts and end in the same vertex
    -- Note: Have to use definitional equality instead of propositional
    -- otherwise the types aren't correct.
    have _isClosed : $s =Q $t := ⟨⟩
    -- Declare w to actually be a closed walk, we know this from above
    have cw : Q(ClosedWalk $G $s) := w
    have _eq : $cw =Q $w := ⟨⟩
    -- Check that it is a cycle, i.e. no repeating vertices
    have isCycle : Q(decide (ClosedWalk.isCycle $cw) = true) := (q(Eq.refl true) : Lean.Expr)
    let c : Q(Cycle $G $s) := q(@Cycle.mk $G $s $cw (of_decide_eq_true ($isCycle)))
    have isHamiltonian : Q(decide (Cycle.isHamiltonian $c) = true) := (q(Eq.refl true) : Lean.Expr)
    have hc : Q(HamiltonianCycle $G) :=
      q(@HamiltonianCycle.mk $G $s (Cycle.mk $cw (of_decide_eq_true ($isCycle))) (of_decide_eq_true $isHamiltonian))
    hc
