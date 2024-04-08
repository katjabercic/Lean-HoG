import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Util.RB

namespace LeanHoG

open Qq

/-- Construct a quoted edge from a pair of numbers -/
def edgeOfData (n : Q(Nat)) : Nat × Nat → Q(Edge $n) :=
  fun (a, b) =>
  have H1 : Q(Nat.blt $a $b = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $n = true) := (q(Eq.refl true) : Lean.Expr)
  q(Edge.mk' $n $a $b $H1 $H2)

/-- Construct a quoted vertex from a number -/
def vertexOfData (G : Q(Graph)) : Nat → Q(Graph.vertex $G) :=
  fun n =>
    have n : Q(Nat) := Lean.mkRawNatLit n
    have H : Q(Nat.blt $n ($G).vertexSize = true) := (q(Eq.refl true) : Lean.Expr)
    q(Fin.mk $n (Nat.le_of_ble_eq_true $H))

/-- Construct a quoted graph from graph data -/
def graphOfData (D : GraphData) : Q(Graph) :=
  have vertexSize : Q(Nat) := Lean.mkRawNatLit D.vertexSize
  have arrQ : Array Q(LeanHoG.Edge $vertexSize) := D.edges.map (LeanHoG.edgeOfData vertexSize)
  have edges : Q(EdgeSet $vertexSize) := build_RBSet arrQ q(Edge.linearOrder $vertexSize)
  q(Graph.mk $vertexSize $edges)

def forallFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] := decide (∀ x, p x)

def forallVertex {G : Graph} (p : G.vertex → Prop) [DecidablePred p] : Bool := decide (∀ v, p v)

def forallEdge {G : Graph} (p : G.edge → Prop) [DecidablePred p] : Bool := decide (∀ e, p e)

end LeanHoG
