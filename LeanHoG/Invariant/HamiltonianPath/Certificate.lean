import Qq
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RB
import LeanHoG.Util.Quote
import LeanHoG.Certificate
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.JsonData

namespace LeanHoG

open Qq
def hamiltonianPathOfData (G : Q(Graph)) (D : HamiltonianPathData) : Q(HamiltonianPath $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  let vertices : List Q(Graph.vertex $G) := D.path.map (finOfData n)
  match vertices.getLast? with
  | none => panic! "no vertices"
  | some t =>
    let ⟨s, w⟩ := walkOfVertexList G t vertices
    let isPath : Q(decide (@Walk.isPath $G $s $t $w) = true) := (q(Eq.refl true) : Lean.Expr)
    let p : Q(Path $G $s $t) := q(@Path.mk $G $s $t $w (of_decide_eq_true $isPath))
    let isHamiltonian : Q(decide (Path.isHamiltonian $p) = true) := (q(Eq.refl true) : Lean.Expr)
    let hp : Q(HamiltonianPath $G) := q(@HamiltonianPath.mk $G $s $t (Path.mk $w (of_decide_eq_true $isPath)) (of_decide_eq_true $isHamiltonian))
    hp
