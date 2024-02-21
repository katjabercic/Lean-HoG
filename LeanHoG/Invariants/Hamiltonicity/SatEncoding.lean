import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Connectivity
import LeanHoG.Invariants.Hamiltonicity.Definition
import Lean

import LeanSAT

namespace LeanHoG

open Lean LeanSAT Encode VEncCNF Meta

/-- `Var i j = true` means: "at position j on the path is vertex i". -/
structure Var (n : Nat) where
  vertex : Fin n
  pos : Fin n
deriving DecidableEq

instance {g : Graph} :  MyFinEnum.FinEnum (Var g.vertexSize) := .ofEquiv {
  toFun := fun {vertex,pos} => (vertex,pos)
  invFun := fun (vertex,pos) => {vertex,pos}
  left_inv := by intro; simp
  right_inv := by intro; simp
}

def verticesAtPosition {n : Nat} (j : Fin n) : List (Literal <| Var n) :=
  List.finRange n |>.map (Literal.pos <| Var.mk · j)

def vertexAtPositions {n : Nat} (i : Fin n) : List (Literal <| Var n) :=
  List.finRange n |>.map (Literal.pos <| Var.mk i ·)

def list_of_distinct_vertices_encoding (g : Graph) : VEncCNF (Literal (Var g.vertexSize)) Unit (fun τ =>
    (∀ i, ∃ j, τ (Var.mk i j)) ∧
    (∀ i, atMost 1 (Multiset.ofList <| vertexAtPositions i) τ) ∧
    (∀ j, ∃ i, τ (Var.mk i j)) ∧
    (∀ j, atMost 1 (Multiset.ofList <| verticesAtPosition j) τ)
  ) :=
  seq[
    for_all (List.toArray <| List.finRange g.vertexSize) fun i =>
      addClause (List.toArray (vertexAtPositions i)),
    for_all (List.toArray <| List.finRange g.vertexSize) fun i =>
      amoPairwise (List.toArray (vertexAtPositions i)),
    for_all (List.toArray <| List.finRange g.vertexSize) fun j =>
      addClause (List.toArray (verticesAtPosition j)),
    for_all (List.toArray <| List.finRange g.vertexSize) fun j =>
      amoPairwise (List.toArray (verticesAtPosition j))
  ]
  |>.mapProp (by
    ext τ
    simp [vertexAtPositions, verticesAtPosition, Clause.satisfies_iff, LitVar.satisfies_iff,
          LitVar.toVar, LitVar.polarity]
  )

def path_encoding (g : Graph) : VEncCNF (Literal (Var g.vertexSize)) Unit (fun τ =>
    (∀ k k', k.val + 1 =  k'.val →
      ∀ i j, ¬ g.badjacent i j → ¬ (τ (Var.mk i k)) ∨ ¬ (τ (Var.mk j k'))
    )
  ) :=
  seq[
    for_all (List.toArray <| List.finRange g.vertexSize) (fun k =>
    for_all (List.toArray <| List.finRange g.vertexSize) fun k' =>
      guard (k.val + 1 = k'.val) (fun h =>
        for_all (List.toArray <| List.finRange g.vertexSize) fun i =>
        for_all (List.toArray <| List.finRange g.vertexSize) fun j =>
          guard (¬g.badjacent i j) (fun h' =>
            addClause (#[Var.mk i k, Var.mk j k'].map LitVar.mkNeg)
          )
      )
    )
  ]
  |>.mapProp (by
    ext τ
    apply Iff.intro
    · intros h k k' seq i j adj
      simp_all [vertexAtPositions, verticesAtPosition, Clause.satisfies_iff, LitVar.satisfies_iff,
            LitVar.toVar, LitVar.polarity, LitVar.mkNeg, not_false_eq_true, implies_true, and_self,
            LitVar.mkPos_or_mkNeg
      ]
      have := h k k'
      simp [seq] at this
      have foo := this i j
      simp [adj] at foo
      let ⟨l, cond⟩ := foo
      unhygienic with_reducible aesop_destruct_products
      unhygienic aesop_cases left <;> [(unhygienic aesop_cases left_1); (unhygienic aesop_cases left_1)]
      · aesop_subst [h_1, h_2]
        simp_all only [true_or]
      · aesop_subst [h_1, h_2]
        simp_all only [or_self]
      · aesop_subst [h_2, h_1]
        simp_all only [or_self]
      · aesop_subst [h_2, h_1]
        simp_all only [or_true]
    · intros h
      simp_all [vertexAtPositions, verticesAtPosition, Clause.satisfies_iff, LitVar.satisfies_iff,
            LitVar.toVar, LitVar.polarity, LitVar.mkNeg, not_false_eq_true, implies_true, and_self,
            LitVar.mkPos_or_mkNeg
      ]
      intros k k'
      have := h k k'
      have foo : k.val + 1 ≠ k'.val ∨ k.val + 1 = k'.val := by apply Or.symm; apply Decidable.em
      cases' foo with neq eq
      simp [neq]
      simp [eq]
      intros i j
      have moo : g.badjacent i j ∨ ¬ g.badjacent i j := by apply Decidable.em
      cases' moo with adj nadj
      simp [adj]
      simp [nadj]
      simp at nadj
      have bar := this eq i j nadj
      cases' bar with l r
      · simp_all only [implies_true, forall_true_left]
        apply Exists.intro
        apply And.intro
        apply Or.inl
        apply Eq.refl
        simp_all only
      · simp_all only [implies_true, forall_true_left]
        apply Exists.intro
        apply And.intro
        apply Or.inr
        apply Eq.refl
        simp_all only
  )

def hamiltonian_path_encoding (g : Graph) := seq (list_of_distinct_vertices_encoding g) (path_encoding g)

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
            let w := (Walk.left h (h' ▸ p.walk))
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

def tryFindHamiltonianPath [Solver IO] (g : Graph) :
  -- IO (Option ((g : Graph) ×' (¬ ∃ (u v : g.vertex) (p : Path g u v), p.isHamiltonian))) := do
  -- Elab.Term.TermElabM (Option (HamiltonianPath g)) := Core.liftIOCore do
  IO (Option (HamiltonianPath g)) := do
  let enc := hamiltonian_path_encoding g
  let foo := EncCNF.run enc.val
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
    if h : 0 < g.vertexSize then
      let mut path : Array (g.vertex) := Array.mkArray g.vertexSize ⟨0, h⟩
      for i in List.fins g.vertexSize do
        for j in List.fins g.vertexSize do
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
