import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.Correctness
import Lean

import LeanSAT

namespace LeanHoG

open Lean LeanSAT Encode VEncCNF Meta Model PropFun

/-- `Var i j = true` means: "at position j on the path is vertex i". -/
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

def hamiltonianPathCNF (G : Graph) : VCnf G.vertexSize (hamiltonianPathConstraints G) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G
  ])
  |> mapProp (by aesop)

--------------------------------------------------------------------------------
-- Now produce an assignment from a Hamiltonian path

abbrev posToVar {n : Nat} : Pos n → Var n := fun ⟨i,j⟩ => ⟨i,j⟩
abbrev varToPos {n : Nat} : Var n → Pos n := fun ⟨i,j⟩ => ⟨i,j⟩

@[simp] def posToVarAssignment {n : Nat} : PropAssignment (Pos n) → PropAssignment (Var n) :=
  fun τ => τ ∘ varToPos

def has_hamiltonian_path_to_hamiltonianPath_constraints {G : Graph} :
  (∃ (τ : PropAssignment (Pos G.vertexSize)), τ ⊨ has_hamiltonian_path G) →
  (∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) := by
  intro h
  rcases h with ⟨τ, h⟩
  let σ := (posToVarAssignment τ)
  exists σ
  aesop

/-- State the correctness theorem in terms of the constraints defined above. -/
theorem hamiltonian_path_to_var_assignment {G : Graph} :
  (∃ (_ : HamiltonianPath G), True) →
  (∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) := by
  intro h
  rcases h with ⟨hp,_⟩
  have exists_τ := hamiltonian_path_to_sat G hp
  apply has_hamiltonian_path_to_hamiltonianPath_constraints exists_τ

-- unsat_to_no_hamiltonian_path
theorem no_assignment_implies_no_hamiltonian_path {G : Graph} :
  (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) →
  (¬ ∃ (_ : HamiltonianPath G), True) := by
  apply imp_neg hamiltonian_path_to_var_assignment

lemma helper {G : Graph} :
  (∃ (_ : HamiltonianPath G), True) ↔
  (∃ (u v : G.vertex) (p : Path G u v), p.isHamiltonian) := by
  apply Iff.intro
  intro h
  rcases h with ⟨⟨u, v, p, cond⟩, _⟩
  use u,v,p,cond
  intro h
  rcases h with ⟨u,v,p,cond⟩
  have hp : HamiltonianPath G := { path := p, isHamiltonian := cond }
  use hp

theorem no_assignment_implies_no_hamiltonian_path' {G : Graph} :
  (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G) →
  (¬ ∃ (u v : G.vertex) (p : Path G u v), p.isHamiltonian) := by
  -- TODO: This proof can definitely be made nicer.
  have := @Iff.imp
    ((¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G))
    ((¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G))
    (¬ ∃ (_ : HamiltonianPath G), True)
    (¬ ∃ (u v : G.vertex) (p : Path G u v), p.isHamiltonian)
    (Iff.refl _)
    (Iff.not helper)
  apply Iff.mp this
  apply no_assignment_implies_no_hamiltonian_path

------------------------------------------------------------------------------
-- By adding an axiom show that if the SAT solver and proof checker say there
-- is no solution to the constraints, then there is no Hamiltonian path

/--
  Given a list of vertices of a graph, try to construct a `Path` in the graph from them.
  If the construction fails, return `none`.
-/
def buildPath {g : Graph} : Option (List (g.vertex)) → Option (HamiltonianPath g)
  | none => none
  | some [] => none
  | some (v :: vs) =>
    let rec fold (t : g.vertex) :
      List (g.vertex) → Option ((s : g.vertex) ×' Path g s t)
    | [] => none
    | [v] =>
      if h : v = t then
        some ⟨v , (h ▸ Path.trivialPath v)⟩
      else
        dbg_trace "[v] not equal to s and t"
        none
    | u :: v :: vs =>
      if h : g.adjacent u v then
        match fold t (v :: vs) with
        | some ⟨s, p⟩ =>
          if h' : s = v then
            let w := (.step h (h' ▸ p.walk))
            if h' : Walk.isPath w = true then
              some ⟨u, ⟨w, h'⟩⟩
            else
              dbg_trace "walk not path"
              none
          else
            dbg_trace s!"{s} ≠ {v}"
            none
        | none =>
          dbg_trace "recursive path not found"
          none
      else
        dbg_trace s!"not adjacent {u}, {v}"
        none
    match List.getLast? vs with
    | some t =>
      match fold t (v :: vs) with
      | some ⟨_, p⟩ =>
        if h : p.isHamiltonian then
          some { path := p, isHamiltonian := h }
        else
          none
      | none => none
    | none => none

def tryFindHamiltonianPath [Solver IO] (G : Graph) :
  IO (Option (HamiltonianPath G)) := do
  let enc := (hamiltonianPathCNF G).val
  let foo := EncCNF.run enc
  let cnf := foo.2.cnf
  let map := foo.2.vMap
  match ← Solver.solve cnf with
  | .error =>
    IO.println "error"
    return none
  | .unsat =>
    IO.println "unsat"
    return none
  | .sat assn =>
    if h : 0 < G.vertexSize then
      let mut path : Array (G.vertex) := Array.mkArray G.vertexSize ⟨0, h⟩
      for i in List.fins G.vertexSize do
        for j in List.fins G.vertexSize do
          match assn.find? (map (Var.mk i j))  with
          | none => panic! "wtf"
          | some true =>
            path := path.set! j i
          | some false =>
            path := path
      let p := buildPath (some path.toList)
      return p
    else
      return none

end LeanHoG
