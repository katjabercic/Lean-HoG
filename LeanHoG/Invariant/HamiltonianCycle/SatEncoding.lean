import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.HamiltonianCycle.Basic

import Trestle.Model.PropFun
import Trestle.Encode.VEncCNF
import Trestle.Solver.Basic
import LeanHoG.Util.TrestleStd

namespace LeanHoG

/- Namespaced (rather than bare in `LeanHoG` like `HamiltonianPath`'s encoding) because
    the two encodings currently duplicate identically-named definitions (`Var`, `VCnf`,
    `vertexClauses`, `positionConstraints`, ...) that would otherwise clash. The
    duplication itself — a generic `n` vertices × `m` positions grid encoding shared by
    both — is a refactor for later; this namespace just keeps the two from colliding in
    the meantime. -/
namespace HamiltonianCycle

open Lean Trestle Encode VEncCNF Meta Model PropFun

/-- `Var i j = true` means: "at position j on the cycle is vertex i".

The graph has `n` vertices and there are `n+1` positions on the cycle.
-/
structure Var (n : Nat) where
  vertex : Fin n
  pos : Fin (n + 1)
deriving DecidableEq, IndexType

/-- Encode that vertex `i` is at position `j` on the cycle (of length `n`, as the first and last vertex repeat). -/
@[simp] def vertexAtPos {n : Nat} (i : Fin n) (j : Fin (n+1)) : PropFun (Var n) :=
  Var.mk i j

/-- There is some vertex at position `j` on the cycle. -/
@[simp] def positionHasAVertex {n : Nat} (j : Fin (n+1)) : PropPred (Var n) := fun τ =>
  ∃ (i : Fin n), τ ⊨ vertexAtPos i j

/-- There is some vertex at every position on the cycle. -/
@[simp] def eachPositionHasAVertex {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (j : Fin (n+1)), positionHasAVertex j τ

/-- The vertex `i` is at some position on the cycle. -/
@[simp] def vertexIsAtSomePosition {n : Nat} (i : Fin n) : PropPred (Var n) := fun τ =>
  ∃ (j : Fin (n+1)), τ ⊨ vertexAtPos i j

/-- Each vertex is at some position on the cycle. -/
@[simp] def eachVertexIsAtSomePosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), vertexIsAtSomePosition i τ

/-- The first and last position of the cycle should actually have the same vertex. -/
@[simp] def vertexInAtMostOnePositionExceptEndpoints {n : Nat} (i : Fin n) : PropPred (Var n) := fun τ =>
  ∀ (j k : Fin (n+1)), j ≠ k ∧ j.val < n ∧ k.val < n → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos i k)ᶜ

/-- The first and last position of the cycle should actually have the same vertex. -/
@[simp] def eachVertexInAtMostOnePositionExceptEndpoints {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), vertexInAtMostOnePositionExceptEndpoints i τ

/-- There is at most one vertex at position `j`. -/
@[simp] def atMostOneVertexAtPosition {n : Nat} (j : Fin (n+1)) : PropPred (Var n) := fun τ =>
  ∀ (i k : Fin n), i ≠ k → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos k j)ᶜ

/-- There is at most one vertex at every position of the cycle. -/
@[simp] def atMostOneVertexInEachPosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (j : Fin (n+1)), atMostOneVertexAtPosition j τ

/-- Encode that if two vertices are consecutive on the cycle, they are adjacent. -/
@[simp] def nonAdjacentVerticesNotConsecutive {G : Graph} : PropPred (Var G.vertexSize) := fun τ =>
  ∀ (k k': Fin (G.vertexSize+1)), k.val + 1 = k'.val →
    ∀ (i j : Fin G.vertexSize), ¬G.adjacent i j →
      (τ ⊨ ((vertexAtPos i k)ᶜ ⊔ (vertexAtPos j k')ᶜ))

-- These constraints are just because of efficiency
-- We declare that the starting and ending vertex must be vertex 0,
-- since we know that the cycle must go through it anyway, we can do it
-- without loss of generality.

/-- WLOG the cycle starts with vertex `0`, as we can always relabel the vertices so it does. -/
@[simp] def cycleStartsAtVertex0 (G : Graph) (h : 0 < G.vertexSize) :
    PropPred (Var G.vertexSize) := fun τ =>
  τ ⊨ (vertexAtPos ⟨0, h⟩ 0)

/-- WLOG the cycle ends with vertex `0`, as we can always relabel the vertices so it does. -/
@[simp] def cycleEndsAtVertex0 (G : Graph) (h : 0 < G.vertexSize) :
    PropPred (Var G.vertexSize) := fun τ =>
  τ ⊨ (vertexAtPos ⟨0, h⟩ ⟨G.vertexSize, lt_add_one G.vertexSize⟩)

/-- The constraints on the vertices of a graph `G`:

- each vertex of the graph `G` is at some position on the cycle.
- each vertex is at some position on the cycle, except the endpoints. -/
@[simp] def vertexConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachVertexIsAtSomePosition) ∧
  (τ |> eachVertexInAtMostOnePositionExceptEndpoints)

/-- The constraints on the positions of a cycle:

- there is a vertex at each position.
- there is at most one vertex at each position. -/
@[simp] def positionConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachPositionHasAVertex) ∧
  (τ |> atMostOneVertexInEachPosition)

/-- The constraints on the edges of a graph `G`:

- if two vertices are consecutive on the cycle, they are adjacent. -/
@[simp] def edgeConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> nonAdjacentVerticesNotConsecutive)

@[simp] def firstAndLastConstraints (G : Graph) (h : 0 < G.vertexSize) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> cycleStartsAtVertex0 G h) ∧ (τ |> cycleEndsAtVertex0 G h)

/-- A graph has a Hamiltonian cycle if it satisfies all of the above constraints. -/
@[simp] def hamiltonianCycleConstraints (G : Graph) (h : 0 < G.vertexSize) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> vertexConstraints G) ∧ (τ |> positionConstraints G) ∧ (τ |> edgeConstraints G) ∧ (τ |> firstAndLastConstraints G h)

----------------------------------------------------------------------------------------
-- Express the problem as a CNF

open Encode VEncCNF LitVar

abbrev VCnf (n : Nat) := VEncCNF (Var n) Unit

@[simp] def verticesAtPosition {n : Nat} (j : Fin (n+1)) : List (Literal <| Var n) :=
  List.finRange n |>.map (mkPos <| Var.mk · j)

@[simp] def vertexAtPositions {n : Nat} (i : Fin n) : List (Literal <| Var n) :=
  List.finRange (n+1) |>.map (mkPos <| Var.mk i ·)

def vertexClauses (G : Graph) : VCnf G.vertexSize (vertexConstraints G) :=
  ( let U := Array.finRange G.vertexSize
    let V := Array.finRange (G.vertexSize+1)
    seq[
      for_all U fun i =>
        addClause (List.toArray (vertexAtPositions i)),
      for_all U fun i =>
      for_all V fun j =>
      for_all V fun k =>
        VEncCNF.guard (j ≠ k ∧ j.val < (G.vertexSize) ∧ k.val < (G.vertexSize)) fun _ =>
          addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk i k])
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

def positionClauses (G : Graph) : VCnf G.vertexSize (positionConstraints G) :=
  ( let U := Array.finRange G.vertexSize
    let V := Array.finRange (G.vertexSize+1)
    seq[
      for_all V fun j =>
        addClause (List.toArray (verticesAtPosition j)),
      for_all V fun j =>
      for_all U fun i =>
      for_all U fun k =>
        VEncCNF.guard (i ≠ k) fun _ =>
          addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk k j])
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

def edgeClauses (G : Graph) : VCnf G.vertexSize (edgeConstraints G) :=
  ( let U := Array.finRange G.vertexSize
    let V := Array.finRange (G.vertexSize+1)
    for_all V fun k =>
    for_all V fun k' =>
      VEncCNF.guard (k.val + 1 = k'.val) fun _ =>
        for_all U fun i =>
        for_all U fun j =>
          VEncCNF.guard (¬G.adjacent i j) fun _ =>
            addClause (#[mkNeg <| Var.mk i k, mkNeg <| Var.mk j k'])
  )
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

def firstAndLastVertexClauses (G : Graph) (h : 0 < G.vertexSize) : VCnf G.vertexSize (firstAndLastConstraints G h) :=
  (seq[
    addClause #[mkPos <| Var.mk ⟨0, h⟩ 0],
    addClause #[mkPos <| Var.mk ⟨0, h⟩ ⟨G.vertexSize, lt_add_one G.vertexSize⟩]
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun]
  )

def hamiltonianCycleCNF (G : Graph) (h : 0 < G.vertexSize) : VCnf G.vertexSize (hamiltonianCycleConstraints G h) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G, firstAndLastVertexClauses G h
  ])
  |> mapProp (by aesop)

end HamiltonianCycle
end LeanHoG
