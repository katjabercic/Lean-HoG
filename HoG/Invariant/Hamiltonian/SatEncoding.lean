import Mathlib.Data.Matrix.Basic

import HoG.Tactic
import HoG.Graph
import HoG.Walk
import HoG.Invariant.ConnectedComponents
import LeanSAT

namespace HoG

open LeanSAT

def Graph.hamiltonianPathEncodeToSAT (g : Graph) :
  Encode.EncCNF (Fin g.vertexSize → Fin g.vertexSize → IVar) :=
  open Encode.EncCNF in do
  let n := g.vertexSize
  if H : 0 < n then
    let varArr ←
      Array.initM n fun i =>
        Array.initM n fun j =>
          mkVar s!"x_{i},{j}"
    -- xᵢ,ⱼ represents vertex i appearing on the path at position j, as i,j ∈ {1,…,n}
    let vertexAtLoc (i : Fin n) (j : Fin n) := (varArr[i]!)[j]!
    -- ⋀ᵢ (⋁ⱼ (xᵢ,ⱼ)) ↔ every vertex appears somewhere on the path
    for i in List.fins n do
      let vars := (List.fins n).map (vertexAtLoc i) |>.toArray
      addClause (vars.map LitVar.mkPos)
    -- ⋀ᵢ (⋁ⱼ (xⱼ,ᵢ)) ↔ every position on the path is occupied by some vertex
    for i in List.fins n do
      let vars := (List.fins n).map (fun j => vertexAtLoc j i) |>.toArray
      addClause (vars.map LitVar.mkPos)
    -- ⋀_i ⋀_i≠k (¬xᵢ,ⱼ ∨ ¬xᵢ,ₖ) ↔ no vertex appears on the path more than once
    for i in List.fins n do
      for j in List.fins n do
        for k in List.fins n do
          if j ≠ k then
            let clause := #[(vertexAtLoc i j), (vertexAtLoc i k)].map LitVar.mkNeg
            addClause clause
    -- ⋀_i ⋀_i≠k (¬xⱼ,ᵢ ∨ ¬xₖ,ᵢ) ↔ no distinct vertices occupy the same position on the path
    for i in List.fins n do
      for j in List.fins n do
        for k in List.fins n do
          if j ≠ k then
            let clause := #[vertexAtLoc j i, vertexAtLoc k i].map LitVar.mkNeg
            addClause clause
    -- ⋀_(k < n) ⋀_((i,j) ∉ E) (¬xₖ,ᵢ ∨ ¬xₖ₊₁,ⱼ) ↔ non-adjacent vertices cannot be adjacent on the path
    for k in List.fins n do
      if k < n-1 then
        for i in List.fins n do
          for j in List.fins i do
            if (Edge.mk i j) ∉ g.edgeTree then
              let next : Fin n := ⟨ (k + 1) % n, by apply Nat.mod_lt; exact H⟩ -- TODO: hack, make nicer
              let clause := #[vertexAtLoc k i, vertexAtLoc next i].map LitVar.mkNeg
              addClause clause

    return vertexAtLoc
  else
    have h' : g.vertexSize = 0 := by simp_all
    return (by rw [h']; intro x; have := Fin.isLt x; contradiction)

def Graph.hamiltonianCycleEncodeToSAT (g : Graph) :
  Encode.EncCNF (Fin g.vertexSize → Fin (g.vertexSize + 1) → IVar) :=
  open Encode.EncCNF in do
  let n := g.vertexSize
  if H : 0 < n then
    let varArr ←
      Array.initM n fun i =>
        Array.initM (n+1) fun j =>
          mkVar s!"x_{i},{j}"
    -- xᵢ,ⱼ represents vertex i appearing on the path at position j
    -- i ranges from 1 to n, j ranges from 1 to n+1 (as it needs to return to the first vertex)
    let vertexAtLoc (i : Fin n) (j : Fin (n + 1)) := (varArr[i]!)[j]!
    -- The cycle starts and end at vertex 0
    addClause #[LitVar.mkPos (vertexAtLoc ⟨0, H⟩ ⟨0, by simp [H]⟩)]
    addClause #[LitVar.mkPos (vertexAtLoc ⟨0, H⟩ n)]
    -- ⋀ᵢ (⋁ⱼ (xᵢ,ⱼ)) ↔ every vertex appears somewhere on the path
    -- we don't need to consider the last position of the path
    for i in List.fins n do
      let vars := (List.fins n).map (vertexAtLoc i) |>.toArray
      addClause (vars.map LitVar.mkPos)
    -- ⋀ᵢ (⋁ⱼ (xⱼ,ᵢ)) ↔ every position on the path is occupied by some vertex
    for i in List.fins n do
      let vars := (List.fins n).map (fun j => vertexAtLoc j i) |>.toArray
      addClause (vars.map LitVar.mkPos)
    -- ⋀_i ⋀_i≠k (¬xᵢ,ⱼ ∨ ¬xᵢ,ₖ) ↔ no vertex appears on the path more than once
    -- except vertex 0 on the first and last place
    for i in List.fins n do
      for j in List.fins n do
        for k in List.fins n do
          if j ≠ k then
            let clause := #[(vertexAtLoc i j), (vertexAtLoc i k)].map LitVar.mkNeg
            addClause clause
    -- ⋀_i ⋀_i≠k (¬xⱼ,ᵢ ∨ ¬xₖ,ᵢ) ↔ no distinct vertices occupy the same position on the path
    for i in List.fins (n + 1) do
      for j in List.fins n do
        for k in List.fins n do
          if j ≠ k then
            let clause := #[vertexAtLoc j i, vertexAtLoc k i].map LitVar.mkNeg
            addClause clause
    -- ⋀_(k < n) ⋀_((i,j) ∉ E) (¬xₖ,ᵢ ∨ ¬xₖ₊₁,ⱼ) ↔ non-adjacent vertices cannot be adjacent on the path
    for k in List.fins n do
      if k < n-1 then
        for i in List.fins n do
          for j in List.fins i do
            if (Edge.mk i j) ∉ g.edgeTree then
              let next : Fin n := ⟨ (k + 1) % n, by apply Nat.mod_lt; exact H⟩ -- TODO: hack, make nicer
              let clause := #[vertexAtLoc k i, vertexAtLoc next i].map LitVar.mkNeg
              addClause clause
    return vertexAtLoc
  else
    have h' : g.vertexSize = 0 := by simp_all
    return (by rw [h']; intro x; have := Fin.isLt x; contradiction)

def buildPath {g : Graph} : Option (List (g.vertex)) → Option ((u v : g.vertex) ×' Path g u v)
  | none => none
  | some [] => none
  | some (v :: vs) =>
    let rec fold (first last : g.vertex) (p : Path g first last) :
      List (g.vertex) → Option ((u v : g.vertex) ×' Path g u v)
    | [] => some ⟨first, last, p⟩
    | v :: vs =>
      if h : g.adjacent last v then
        have conn_last_v : g.connected last v := g.adjacentConnected h
        let w := Walk.right p.walk conn_last_v
        if h' : Walk.isPath w = true then
          fold first v ⟨w, h'⟩ vs
        else
          none
      else
        none
    fold v v (trivialPath v) vs

def buildCycle {g : Graph} : Option (List (g.vertex)) → Option ((u : g.vertex) ×' Cycle g u)
  | none => none
  | some [] => none
  | some [v] =>
    let walk := Walk.trivial v
    some ⟨v, walk, by simp [List.all_distinct, Walk.vertices]⟩
  | some (v₁ :: v₂ :: vs) =>
    let rec fold (first last : g.vertex) (p : Path g first last) :
      List (g.vertex) → Option ((u v : g.vertex) ×' Path g u v)
    | [] => some ⟨first, last, p⟩
    | v :: vs =>
      if h : g.adjacent last v then
        have conn_last_v : g.connected last v := g.adjacentConnected h
        let w := Walk.right p.walk conn_last_v
        if h' : Walk.isPath w = true then
          fold first v ⟨w, h'⟩ vs
        else
          none
      else
        none
    let path := fold v₂ v₂ (trivialPath v₂) vs
    match path with
    | none => none
    | some ⟨u,v,p⟩ =>
      if h : u = v₂ ∧ v = v₁ ∧ g.adjacent v₁ v₂ then
        have u_eq_v₂ := h.1
        have v_eq_v₁ := h.2.1
        have conn_v₁_v₂ : g.connected v₁ v₂ := g.adjacentConnected h.2.2
        let w : ClosedWalk g v₁ := Walk.left conn_v₁_v₂ (u_eq_v₂ ▸ v_eq_v₁ ▸ p.walk)
        some ⟨ v₁,
          { cycle := w,
            isCycle := by
              subst u_eq_v₂
              subst v_eq_v₁
              exact p.isPath
          }⟩
      else
        none

def findHamiltonianPath [Solver IO] (g : Graph) : IO (Option ((u v : g.vertex) ×' Path g u v)) := do
  let (vertexAtLoc, enc) := Encode.EncCNF.new! (g.hamiltonianPathEncodeToSAT)
  match ← Solver.solve enc.toFormula with
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
          match assn.find? (vertexAtLoc i j) with
          | none => panic! "wtf"
          | some true =>
            path := path.set! j i
          | some false =>
            path := path
      return (buildPath (some path.toList))
    else
      return (buildPath (some []))

def findHamiltonianCycle [Solver IO] (g : Graph) : IO (Option ((u : g.vertex) ×' Cycle g u)) := do
  let (vertexAtLoc, enc) := Encode.EncCNF.new! (g.hamiltonianCycleEncodeToSAT)
  match ← Solver.solve enc.toFormula with
  | .error =>
    IO.println "error"
    return none
  | .unsat =>
    IO.println "unsat"
    return none
  | .sat assn =>
    if h : 0 < g.vertexSize then
      let mut path : Array (g.vertex) := Array.mkArray (g.vertexSize + 1) ⟨0, by simp [h]⟩
      for i in List.fins g.vertexSize do
        for j in List.fins (g.vertexSize + 1) do
          let v := vertexAtLoc i j
          match assn.find? v with
          | none => panic! s!"no assignment for ({i}, {j}) → {v}"
          | some true =>
            path := path.set! j i
          | some false =>
            path := path
      return (buildCycle (some path.toList))
    else
      return (buildCycle (some []))

end HoG
