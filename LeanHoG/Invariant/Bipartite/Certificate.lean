import Qq
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.Basic
import LeanHoG.Util.Quote
import LeanHoG.Util.RB
import LeanHoG.Certificate

namespace LeanHoG

open Qq

/-- Construct a Bipartite certificate from Bipartite data -/
def TwoColoringOfData (G : Q(Graph)) (C : TwoColoringData) : Q(TwoColoring $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have convertToFin : Nat × Nat → Q(Fin $n × Fin 2) := fun (i,j) => q(($(finOfData n i), $(finOfData (Lean.mkRawNatLit 2) j)))
  have colorMap : Q(Std.RBMap (Graph.vertex $G) (Fin 2) Fin.instLinearOrderFin.compare) :=
    build_RBMap (C.color.map convertToFin) q(Fin.instLinearOrderFin)
  have color : Q(Graph.vertex $G → Fin 2) := q(fun v => Std.RBMap.findD $colorMap v 0)
  have edgeColor : Q(Std.RBSet.all (Graph.edgeSet $G) (fun e => $color e.fst ≠ $color e.snd) = true) := (q(Eq.refl true) : Lean.Expr)
  q(@TwoColoring.mk $G (VertexColoring.mk' $G $color (Graph.all_edges $G (fun e => $color e.fst ≠ $color e.snd) $edgeColor)))

def OddClosedWalkOfData (G : Q(Graph)) (W : OddClosedWalkData) : Q(OddClosedWalk $G) :=
  match W.closedWalk.map (vertexOfData G) with
  | [] => panic! "Encountered empty walk"
  | v :: vs =>
    let rec fold (u : Q(Graph.vertex $G)):
      List Q(Graph.vertex $G) → Q(Walk $G $u $v) := fun vs =>
      match vs with
      | [] =>
        let h : Q(decide (@Graph.adjacent $G $u $v) = true) := (q(Eq.refl true) : Lean.Expr)
        q(.step (of_decide_eq_true $h) (.here $v))
      | u' :: us =>
        let w := fold u' us
        let h : Q(decide (@Graph.adjacent $G $u $u') = true) := (q(Eq.refl true) : Lean.Expr)
        q(.step (of_decide_eq_true $h) $w)
    have closedWalk : Q(ClosedWalk $G $v) := fold v vs
    have decideIsOdd : Q(decide (Odd ($closedWalk).length) = true) := (q(Eq.refl true) : Lean.Expr)
    q(OddClosedWalk.mk
      $v
      $closedWalk
      (of_decide_eq_true $decideIsOdd)
    )

end LeanHoG
