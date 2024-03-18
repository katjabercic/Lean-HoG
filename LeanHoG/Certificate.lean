import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RBSet

namespace LeanHoG

open Qq

/-- Construct a quoted edge from a pair of numbers -/
def edgeOfData (n : Q(Nat)) : Nat × Nat → Q(Edge $n) :=
  fun (a, b) =>
  have H1 : Q(Nat.blt $a $b = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $n = true) := (q(Eq.refl true) : Lean.Expr)
  q(Edge.mk' $n $a $b $H1 $H2)

/-- Construct a quoted graph from graph data -/
def graphOfData (D : GraphData) : Q(Graph) :=
  have vertexSize : Q(Nat) := Lean.mkRawNatLit D.vertexSize
  have arrQ : Array Q(LeanHoG.Edge $vertexSize) := D.edges.map (LeanHoG.edgeOfData vertexSize)
  have edges : Q(Std.RBSet (LeanHoG.Edge $vertexSize) LeanHoG.Edge.linearOrder.compare) := build_RBSet arrQ q(LeanHoG.Edge.linearOrder)
  q(Graph.mk $vertexSize $edges)

def forallFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] : Bool := decide (∀ x, p x)
def forallVertex {G : Graph} (p : G.vertex → Prop) [DecidablePred p] : Bool := decide (∀ v, p v)

end LeanHoG
