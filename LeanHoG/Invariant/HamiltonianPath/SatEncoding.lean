import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Util.List

import Trestle.Model.PropFun
import Trestle.Encode.VEncCNF
import Trestle.Solver.Basic
import LeanHoG.Util.TrestleStd

namespace LeanHoG

open Lean Trestle Encode VEncCNF Meta Model PropFun

/-- `Var i j = true` means: "at position j on the path is vertex i". -/
structure Var (n : Nat) where
  vertex : Fin n
  pos : Fin n
deriving DecidableEq, IndexType

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

@[simp] def vertexInAtMostOnePosition {n : Nat} (i : Fin n) : PropPred (Var n) := fun τ =>
  ∀ (j k : Fin n), j ≠ k → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos i k)ᶜ

@[simp] def eachVertexInAtMostOnePosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), vertexInAtMostOnePosition i τ

@[simp] def atMostOneVertexAtPosition {n : Nat} (j : Fin n) : PropPred (Var n) := fun τ =>
  ∀ (i k : Fin n), i ≠ k → τ ⊨ (vertexAtPos i j)ᶜ ⊔ (vertexAtPos k j)ᶜ

@[simp] def atMostOneVertexInEachPosition {n : Nat} : PropPred (Var n) := fun τ =>
  ∀ (i : Fin n), atMostOneVertexAtPosition i τ

/-- Encode that if two vertices are consecutive on the path, they are adjacent. -/
@[simp] def nonAdjacentVerticesNotConsecutive {G : Graph} : PropPred (Var G.vertexSize) := fun τ =>
  ∀ (k k': Fin G.vertexSize), k.val + 1 = k'.val →
    ∀ (i j : Fin G.vertexSize), ¬G.adjacent i j →
      (τ ⊨ ((vertexAtPos i k)ᶜ ⊔ (vertexAtPos j k')ᶜ))

@[simp] def vertexConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachVertexIsAtSomePosition) ∧
  (τ |> eachVertexInAtMostOnePosition)

@[simp] def positionConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> eachPositionHasAVertex) ∧
  (τ |> atMostOneVertexInEachPosition)

@[simp] def edgeConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
  (τ |> nonAdjacentVerticesNotConsecutive)

@[simp] def hamiltonianPathConstraints (G : Graph) : PropPred (Var G.vertexSize) := fun τ =>
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
      VEncCNF.guard (j ≠ k) fun _ =>
        addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk i k])
  ])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
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
    simp [Clause.toPropFun, Array.finRange]
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
    simp [Clause.toPropFun, Array.finRange]
  )

def hamiltonianPathCNF (G : Graph) : VCnf G.vertexSize (hamiltonianPathConstraints G) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G
  ])
  |> mapProp (by aesop)

--------------------------------------------------------------------------------
-- Now produce an assignment from a Hamiltonian path

/-- Every Hamiltonian path in `G` gives a satisfying assignment of
`hamiltonianPathConstraints`: read the path off as "vertex `i` sits at position `j`".

Mirrors `HamiltonianCycle.hamiltonian_cycle_to_sat`, and is shorter than it in two ways.
There is no rotation step, the path encoding fixing no vertex; and the at-most-one-position
constraint holds of every position rather than all but the endpoints, so distinctness of the
whole vertex list settles it where the cycle needs distinctness of the tail. -/
theorem hamiltonian_path_to_sat {G : Graph} (hp : HamiltonianPath G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G := by
  let n := G.vertexSize
  let l := hp.path.walk.vertices
  have l_len : n = l.length := by
    apply Eq.symm HamiltonianPath.length_eq_num_vertices
  let τ : PropAssignment (Var G.vertexSize) := fun ⟨i, j⟩ =>
    if l.get (Fin.cast l_len j) = i then true else false
  have τ_vertex : τ |> vertexConstraints G := by
    constructor
    · intro i
      obtain ⟨j, hj⟩ := List.get_of_mem (hp.isHamiltonian i)
      use (Fin.cast l_len.symm j)
      simp only [List.get_eq_getElem] at hj
      simpa [τ, hj]
    · simp
      intro i j k hjk
      by_contra
      have had : l.all_distinct := by apply hp.path.isPath
      simp [τ] at this
      have hinj := List.all_distinct_get_injective
        (h := had)
        (i := Fin.cast l_len j)
        (j := Fin.cast l_len k)
      simp [this] at hinj
      contradiction

  have τ_positions : τ |> positionConstraints G := by
    constructor
    · intro j
      set i := l[j] with h
      use i
      simpa [τ]
    · intro j i i' hne
      by_contra
      simp [τ] at this
      have : i = i' := by rw [← this.1, ← this.2]
      contradiction

  have τ_edge : τ |> edgeConstraints G := by
    simp
    intro k k' hk i i' hi
    by_contra
    simp [τ] at this
    have hadj' : G.adjacent (l.get (Fin.cast l_len k)) (l.get (Fin.cast l_len k')) := by
      apply Walk.consecutive_vertices_adjacent
      simp [hk]
    aesop

  use τ
  exact ⟨τ_vertex, τ_positions, τ_edge⟩

/-- State the correctness theorem in terms of the constraints defined above. -/
theorem hamiltonian_path_to_var_assignment {G : Graph} :
  (∃ (_ : HamiltonianPath G), True) →
  (∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) := by
  intro h
  rcases h with ⟨hp,_⟩
  exact hamiltonian_path_to_sat hp

theorem no_assignment_implies_no_hamiltonian_path {G : Graph} :
  (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) →
  (¬ ∃ (_ : HamiltonianPath G), True) := by
  apply mt hamiltonian_path_to_var_assignment

theorem no_assignment_implies_no_hamiltonian_path' {G : Graph} :
  (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) →
  (¬ ∃ (u v : G.vertex) (p : Path G u v), p.isHamiltonian) := by
  intro h
  have contr := no_assignment_implies_no_hamiltonian_path h
  simp at contr
  cases contr with
  | mk h =>
    intro expham
    obtain ⟨u, v, ⟨p, cond⟩⟩ := expham
    cases h { u := u, v := v, path := p, isHamiltonian := cond }

end LeanHoG
