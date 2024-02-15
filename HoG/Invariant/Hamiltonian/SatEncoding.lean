import HoG.Graph
import HoG.Walk
import HoG.Invariant.ConnectedComponents
import HoG.Invariant.Hamiltonian.Definition

import LeanSAT

namespace HoG

open LeanSAT Encode VEncCNF

/-- (Var i j = true) means: "at position j on the path is vertex i". -/
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

def encoding1 (g : Graph) : VEncCNF (Literal (Var g.vertexSize)) Unit (fun τ =>
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

def encoding2 (g : Graph) : VEncCNF (Literal (Var g.vertexSize)) Unit (fun τ =>
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

def my_enc (g : Graph) := seq (encoding1 g) (encoding2 g)

def showNoHamiltonianPath [Solver IO] (g : Graph) :
  -- IO (Option ((g : Graph) ×' (¬ ∃ (u v : g.vertex) (p : Path g u v), p.isHamiltonian))) := do
  IO Unit := do
  let enc := my_enc g
  let cnf := enc.val.toICnf
  -- IO.println s!"{enc}"
  match ← Solver.solve cnf with
  | .error =>
    IO.println "error"
  | .unsat =>
    IO.println "unsat"
  | .sat _ =>
    return ()

-- /--
--   For a given graph `g` encode finding a Hamiltonian cycle as a SAT problem.
-- -/
-- def Graph.hamiltonianCycleEncodeToSAT (g : Graph) :
--   Encode.EncCNF (Fin g.vertexSize → Fin (g.vertexSize + 1) → IVar) :=
--   open Encode.EncCNF in do
--   let n := g.vertexSize
--   if H : 0 < n then
--     let varArr ←
--       Array.initM n fun i =>
--         Array.initM (n+1) fun j =>
--           mkVar s!"x_{i},{j}"
--     -- xᵢ,ⱼ represents vertex i appearing on the path at position j
--     -- i ranges from 1 to n, j ranges from 1 to n+1 (as it needs to return to the first vertex)
--     let vertexAtLoc (i : Fin n) (j : Fin (n + 1)) := (varArr[i]!)[j]!
--     -- The cycle starts and end at vertex 0
--     addClause #[LitVar.mkPos (vertexAtLoc ⟨0, H⟩ ⟨0, by simp [H]⟩)]
--     addClause #[LitVar.mkPos (vertexAtLoc ⟨0, H⟩ n)]
--     -- ⋀ᵢ (⋁ⱼ (xᵢ,ⱼ)) ↔ every vertex appears somewhere on the path
--     -- we don't need to consider the last position of the path
--     for i in List.fins n do
--       let vars := (List.fins n).map (vertexAtLoc i) |>.toArray
--       addClause (vars.map LitVar.mkPos)
--     -- ⋀ᵢ (⋁ⱼ (xⱼ,ᵢ)) ↔ every position on the path is occupied by some vertex
--     for i in List.fins n do
--       let vars := (List.fins n).map (fun j => vertexAtLoc j i) |>.toArray
--       addClause (vars.map LitVar.mkPos)
--     -- ⋀_i ⋀_j≠k (¬xᵢ,ⱼ ∨ ¬xᵢ,ₖ) ↔ no vertex appears on the path more than once
--     -- except vertex 0 on the first and last place
--     for i in List.fins n do
--       for j in List.fins n do
--         for k in List.fins n do
--           if j ≠ k then
--             let clause := #[(vertexAtLoc i j), (vertexAtLoc i k)].map LitVar.mkNeg
--             addClause clause
--     -- ⋀_i ⋀_j≠k (¬xⱼ,ᵢ ∨ ¬xₖ,ᵢ) ↔ no distinct vertices occupy the same position on the path
--     for i in List.fins (n + 1) do
--       for j in List.fins n do
--         for k in List.fins n do
--           if j ≠ k then
--             let clause := #[vertexAtLoc j i, vertexAtLoc k i].map LitVar.mkNeg
--             addClause clause
--     -- ⋀_(k < n) ⋀_((i,j) ∉ E) (¬xₖ,ᵢ ∨ ¬xₖ₊₁,ⱼ) ↔ non-adjacent vertices cannot be adjacent on the path
--     for k in List.fins n do
--       if k < n-1 then
--         for i in List.fins n do
--           for j in List.fins i do
--             if (Edge.mk i j) ∉ g.edgeTree then
--               let next : Fin n := ⟨ (k + 1) % n, by apply Nat.mod_lt; exact H⟩ -- TODO: hack, make nicer
--               let clause := #[vertexAtLoc k i, vertexAtLoc next i].map LitVar.mkNeg
--               addClause clause
--     return vertexAtLoc
--   else
--     have h' : g.vertexSize = 0 := by simp_all
--     return (by rw [h']; intro x; have := Fin.isLt x; contradiction)

-- /--
--   Given a list of vertices of a graph, try to construct a `Path` in the graph from them.
--   If the construction fails, return `none`.
-- -/
-- def buildPath {g : Graph} : Option (List (g.vertex)) → Option ((u v : g.vertex) ×' Path g u v)
--   | none => none
--   | some [] => none
--   | some (v :: vs) =>
--     let rec fold (first last : g.vertex) (p : Path g first last) :
--       List (g.vertex) → Option ((u v : g.vertex) ×' Path g u v)
--     | [] => some ⟨first, last, p⟩
--     | v :: vs =>
--       if h : g.adjacent last v then
--         let w := Walk.right p.walk h
--         if h' : Walk.isPath w = true then
--           fold first v ⟨w, h'⟩ vs
--         else
--           none
--       else
--         none
--     fold v v (Path.trivialPath v) vs

-- /--
--   Given a list of vertices of a graph, try to construct a `Cycle` in the graph from them.
--   If the construction fails, return `none`.
-- -/
-- def buildCycle {g : Graph} : Option (List (g.vertex)) → Option ((u : g.vertex) ×' Cycle g u)
--   | none => none
--   | some [] => none
--   | some [v] =>
--     let walk := Walk.trivial v
--     some ⟨v, walk, by simp [List.all_distinct, Walk.vertices]⟩
--   | some (v₁ :: v₂ :: vs) =>
--     let rec fold (first last : g.vertex) (p : Path g first last) :
--       List (g.vertex) → Option ((u v : g.vertex) ×' Path g u v)
--     | [] => some ⟨first, last, p⟩
--     | v :: vs =>
--       if h : g.adjacent last v then
--         let w := Walk.right p.walk h
--         if h' : Walk.isPath w = true then
--           fold first v ⟨w, h'⟩ vs
--         else
--           none
--       else
--         none
--     let path := fold v₂ v₂ (Path.trivialPath v₂) vs
--     match path with
--     | none => none
--     | some ⟨u,v,p⟩ =>
--       if h : u = v₂ ∧ v = v₁ ∧ g.adjacent v₁ v₂ then
--         have u_eq_v₂ := h.1
--         have v_eq_v₁ := h.2.1
--         let w : ClosedWalk g v₁ := Walk.left h.2.2 (u_eq_v₂ ▸ v_eq_v₁ ▸ p.walk)
--         if cyc : w.isCycle then
--         some ⟨ v₁,
--           { cycle := w,
--             isCycle := by
--               subst u_eq_v₂
--               subst v_eq_v₁
--               exact cyc
--           }⟩
--         else
--           none
--       else
--         none

-- /--
--   Given a graph `g`, encode the problem of finding a Hamiltonian path as a SAT
--   problem and then from the solution construct a `HamiltonianPath` in the graph.
-- -/
-- def findHamiltonianPath [Solver IO] (g : Graph) :
--   IO (Option ((u v : g.vertex) ×' HamiltonianPath u v)) := do
--   let (vertexAtLoc, enc) := Encode.EncCNF.new! (g.hamiltonianPathEncodeToSAT)
--   -- IO.println s!"{enc}"
--   match ← Solver.solve enc.toFormula with
--   | .error =>
--     IO.println "error"
--     return none
--   | .unsat =>
--     IO.println "unsat"
--     return none
--   | .sat assn =>
--     if h : 0 < g.vertexSize then
--       let mut path : Array (g.vertex) := Array.mkArray g.vertexSize ⟨0, h⟩
--       for i in List.fins g.vertexSize do
--         for j in List.fins g.vertexSize do
--           match assn.find? (vertexAtLoc i j) with
--           | none => panic! "wtf"
--           | some true =>
--             path := path.set! j i
--           | some false =>
--             path := path
--       let p := (buildPath (some path.toList))
--       match p with
--       | none => return none
--       | some ⟨u,v,p⟩ =>
--         if h' : p.isHamiltonian then
--           return some ⟨u,v,p,h'⟩
--         else
--           return none
--     else
--       return none

-- /--
--   Given a graph `g`, encode the problem of finding a Hamiltonian cycle as a SAT
--   problem and then from the solution construct a `HamiltonianCycle` in the graph.
-- -/
-- def findHamiltonianCycle [Solver IO] (g : Graph) :
--   IO (Option ((u : g.vertex) ×' HamiltonianCycle g u)) := do
--   let (vertexAtLoc, enc) := Encode.EncCNF.new! (g.hamiltonianCycleEncodeToSAT)
--   match ← Solver.solve enc.toFormula with
--   | .error =>
--     IO.println "error"
--     return none
--   | .unsat =>
--     IO.println "unsat"
--     return none
--   | .sat assn =>
--     if h : 0 < g.vertexSize then
--       let mut path : Array (g.vertex) := Array.mkArray (g.vertexSize + 1) ⟨0, by simp [h]⟩
--       for i in List.fins g.vertexSize do
--         for j in List.fins (g.vertexSize + 1) do
--           let v := vertexAtLoc i j
--           match assn.find? v with
--           | none => panic! s!"no assignment for ({i}, {j}) → {v}"
--           | some true =>
--             path := path.set! j i
--           | some false =>
--             path := path
--       let c := (buildCycle (some path.toList))
--       match c with
--       | none => return none
--       | some ⟨u,c⟩ =>
--         if h' : c.isHamiltonian then
--           return some ⟨u, c, h'⟩
--         else
--           return none
--     else
--       return none

end HoG
