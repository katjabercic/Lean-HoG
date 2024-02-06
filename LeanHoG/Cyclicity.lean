import LeanHoG.Graph
import LeanHoG.Edge

namespace LeanHoG

def cycleEdgeTree (n: Nat) (k : Fin n.succ) : SetTree (Edge (n + 3)) :=
  if h : k = 0 then
    .node
      (Edge.fromNats 0 (n+2) (by linarith) (by linarith))
      (.leaf (Edge.fromNats 0 1 (by linarith) (by linarith)))
      (.leaf (Edge.fromNats 1 2 (by linarith) (by linarith)))
  else
    .node
      (Edge.fromNats (k+1) (k+2) (by linarith) (by linarith [k.prop]))
      (cycleEdgeTree n (k-1))
      .empty
termination_by _ n k => k.val
decreasing_by
  apply Fin.sub_one_lt_iff.mpr
  apply Fin.pos_iff_ne_zero.mpr
  assumption

lemma cycleEdgeCorrect (n : Nat) (k : Nat) (h : k < n.succ) : (cycleEdgeTree n ⟨k, h⟩).isCorrect := by
  induction k
  · sorry
  · sorry

/-- The standard cycle graph on n+3 vertices. -/
def Cycle (n : Nat) : Graph :=
  {
    vertexSize := n + 3,
    edgeTree := cycleEdgeTree n n,
    edgeCorrect := by apply cycleEdgeCorrect
  }

#eval (Cycle 4).edgeTree



/-- Is the list of vertices a path of length at least 3 ? -/
def Graph.is_3_path {G: Graph}: List G.vertex → Bool
  | a :: b :: c :: d :: t => a ≠ b && b ≠ c && c ≠ d && G.adjacent a b && G.is_3_path (b::c::d::t)
  | [a, b, c] => a ≠ b && b ≠ c && G.adjacent a b && G.adjacent b c
  | _ => false

/-- Is the last element equal to first parameter -/
def Graph.is_closed_list {G: Graph}: Nat → List G.vertex → Bool
  | _, [] => false
  | s, [l] => s == l
  | s, _::t => Graph.is_closed_list s t

/-- Does the list form a cycle ? -/
def Graph.is_cycle_list {G: Graph}: List G.vertex → Bool
  | [] => false
  | h::t => Graph.is_closed_list h t && Graph.is_3_path (h::t)

/-
class CyclicCertificateOld (G: Graph) where

  first: G.vertex

  length: Fin (G.vertexSize + 1)

  pos: Fin (G.vertexSize + 1) → G.vertex

  firstPos: pos 1 = first

  lastPos: pos length = first

  cyclic: G.vertexSize > 2 → ∀ x: Fin (G.vertexSize + 1), 1 < x && x < length →
  G.adjacent (pos x) (pos (x+1))
-/

class CyclicCertificate (G: Graph) where

  list: List G.vertex

  isCycle: G.is_cycle_list list

  /- We also need at least three distinct vertices -/

/- NOT WORKING
class Cycle {G: Graph} where
  edges: List G.edgeType

  longEnough: 3 ≤ edges.length

  closed: (edges[0]'longEnough).fst = edges[edges.length-1].snd
-/

/- NOT WORKING
def Graph.is_cycle_old {G: Graph} {edges: List G.edgeType}: Bool:=
    if edges.length < 3 then
      false
    else
      edges[0].fst
-/

def Graph.is_cyclic (G: Graph):=
  ∃ l: List G.vertex, G.is_cycle_list l

instance {G: Graph} [C: CyclicCertificate G]: Graph.is_cyclic G:=
  Exists.intro C.list C.isCycle
