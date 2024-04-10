import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.HamiltonianCycle.Basic
import Lean

import LeanSAT

namespace LeanHoG
namespace HamiltonianCycle

open Lean LeanSAT Encode VEncCNF Meta Model PropFun

/-- `Var i j = true` means: "at position j on the cycle is vertex i".
-/
structure Var (n : Nat) where
  vertex : Fin n
  pos : Fin n
deriving DecidableEq, LeanColls.IndexType

@[simp] def vertexAtPos {n : Nat} (i j : Fin n) : PropFun (Var n) :=
  Var.mk i j

@[simp] def positionHasAVertex {n : Nat} (j : Fin n) : PropPred (Var n) := fun τ =>
  ∃ (i : Fin n), τ ⊨ vertexAtPos i j

@[simp] def eachPositionHasAVertex {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (j : Fin n), positionHasAVertex j τ

@[simp] def vertexIsAtSomePosition {n : Nat} (i : Fin n) : PropPred (Var n) := fun τ =>
  ∃ (j : Fin n), τ ⊨ vertexAtPos i j

@[simp] def eachVertexIsAtSomePosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), vertexIsAtSomePosition i τ

/-- The first and last position of the cycle should actually have the same vertex. -/
@[simp] def vertexInAtMostOnePositionExceptEndpoints {n : Nat} (i : Fin n) : PropPred (Var n) := fun τ =>
  ∀ (j k : Fin n), j ≠ k ∧ j < (n-1) ∧ k < (n-1) → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos i k)ᶜ

/-- The first and last position of the cycle should actually have the same vertex. -/
@[simp] def eachVertexInAtMostOnePositionExceptEndpoints {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), vertexInAtMostOnePositionExceptEndpoints i τ

@[simp] def atMostOneVertexAtPosition {n : Nat} (j : Fin n) : PropPred (Var n) := fun τ =>
  ∀ (i k : Fin n), i ≠ k → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos k j)ᶜ

@[simp] def atMostOneVertexInEachPosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), atMostOneVertexAtPosition i τ

/-- Encode that if two vertices are consecutive on the cycle, they are adjacent. -/
@[simp] def nonAdjacentVerticesNotConsecutive {G : Graph} : PropPred (Var G.vertexSize) := fun τ =>
  ∀ (k k': Fin G.vertexSize), k.val + 1 = k'.val →
    ∀ (i j : Fin G.vertexSize), ¬G.adjacent i j →
      (τ ⊨ ((vertexAtPos i k)ᶜ ⊔ (vertexAtPos j k')ᶜ))

-- These constraints are just because of efficiency
-- We declare that the starting and ending vertex must be vertex 0,
-- since we know that the cycle must go through it anyway, we can do it
-- without loss of generality.

-- def cycleStartsAtVertex0 {G : Graph} : PropPred (Var G.vertexSize) := fun τ =>
--   τ ⊨ (vertexAtPos 0 0)

-- def cycleEndsAtVertex0 {G : Graph} : PropPred (Var G.vertexSize) := fun τ =>
--   τ ⊨ (vertexAtPos 0 (G.vertexSize - 1))

@[simp] def vertexConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachVertexIsAtSomePosition) ∧
  (τ |> eachVertexInAtMostOnePositionExceptEndpoints)

@[simp] def positionConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachPositionHasAVertex) ∧
  (τ |> atMostOneVertexInEachPosition)

@[simp] def edgeConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> nonAdjacentVerticesNotConsecutive)

@[simp] def hamiltonianCycleConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> vertexConstraints G) ∧ (τ |> positionConstraints G) ∧ (τ |> edgeConstraints G)

----------------------------------------------------------------------------------------
-- Express the problem as a CNF

open Encode VEncCNF LitVar

abbrev VCnf (n : Nat) := VEncCNF (Var n) Unit

@[simp] def verticesAtPosition {n : Nat} (j : Fin n) : List (Literal <| Var n) :=
  List.finRange n |>.map (mkPos <| Var.mk · j)

@[simp] def vertexAtPositions {n : Nat} (i : Fin n) : List (Literal <| Var n) :=
  List.finRange n |>.map (mkPos <| Var.mk i ·)

def vertexClauses (G : Graph) : VCnf G.vertexSize (vertexConstraints G) :=
  (let U := Array.finRange G.vertexSize
  seq[
    for_all U fun i =>
      addClause (List.toArray (vertexAtPositions i)),
    for_all U fun i =>
    for_all U fun j =>
    for_all U fun k =>
      VEncCNF.guard (j ≠ k ∧ j < (G.vertexSize-1) ∧ k < (G.vertexSize-1)) fun _ =>
        addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk i k])
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun]
    intro _
    apply Iff.intro
    intro h' i j k j_neq_k j_not_last k_not_last
    have := h' i j k
    simp [j_neq_k, j_not_last, k_not_last] at this
    exact this
    intro h' i j k
    split
    simp
    next h'' => simp [h', h'']
    simp_all only [Pi.top_apply, top]
  )

def positionClauses (G : Graph) : VCnf G.vertexSize (positionConstraints G) :=
  (let U := Array.finRange G.vertexSize
  seq[
    for_all U fun j =>
      addClause (List.toArray (verticesAtPosition j)),
    for_all U fun j =>
    for_all U fun i =>
    for_all U fun k =>
      VEncCNF.guard (i ≠ k) fun _ =>
        addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk k j])
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun]
    intro _
    apply Iff.intro
    intro h' i j k j_neq_k
    have := h' i j k
    simp [j_neq_k] at this
    exact this
    intro h' i j k
    split
    simp
    next h'' => simp [h', h'']
  )

def edgeClauses (G : Graph) : VCnf G.vertexSize (edgeConstraints G) :=
  ( let U := Array.finRange G.vertexSize
    for_all U fun k =>
    for_all U fun k' =>
      VEncCNF.guard (k.val + 1 = k'.val) fun _ =>
        for_all U fun i =>
        for_all U fun j =>
          VEncCNF.guard (¬G.adjacent i j) fun _ =>
            addClause (#[mkNeg <| Var.mk i k, mkNeg <| Var.mk j k'])
  )
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun]
    apply Iff.intro
    intro h k k' h'' i j h'''
    have := h k k'
    simp [h''] at this
    have := this i j
    simp [h''] at this
    rename_i this_1
    simp_all only [↓reduceIte]
    aesop
  )

def hamiltonianCycleCNF (G : Graph) : VCnf G.vertexSize (hamiltonianCycleConstraints G) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G
  ])
  |> mapProp (by aesop)


end HamiltonianCycle
end LeanHoG
