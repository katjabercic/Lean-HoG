import Lean
import Mathlib.Order.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Prod.Lex
import Mathlib.Init.Algebra.Order
import Init.Prelude
import Tactic

import TreeSet
import TreeMap

-- The endpoints of an edge must be sorted
structure Edge (vertexSize : ℕ) : Type :=
  fst : Fin vertexSize
  snd : Fin fst

macro "Edge[" n:term "," i:term "," j:term "]" : term =>
 `(@Edge.mk $n (@Fin.mk $n $i (by trivial)) (@Fin.mk $i $j (by trivial)))

@[simp]
def nat_compare (i j : ℕ) : Ordering :=
  if i < j then .lt else (if i = j then .eq else .gt)

@[simp]
def Edge.compare {m : ℕ} (u v : Edge m) : Ordering :=
  match nat_compare u.fst v.fst with
  | .lt => .lt
  | .eq => nat_compare u.snd v.snd
  | .gt => .gt

@[simp]
instance Edge_Ord (m : ℕ): Ord (Edge m) where
  compare := Edge.compare

structure Graph : Type :=
  vertexSize : ℕ
  edgeTree : Tree (Edge vertexSize)
  edgeCorrect : edgeTree.correct := by rfl

@[simp, reducible]
def Graph.vertex (G : Graph) := Fin G.vertexSize

instance Graph_vertex_LinearOrder (G : Graph) : LinearOrder (Graph.vertex G) :=
  by simp ; infer_instance -- this seems suboptimal

@[simp]
def Graph.edgeType (G : Graph) := Edge G.vertexSize

@[simp]
def Graph.edge (G : Graph) := { e : G.edgeType | e ∈ G.edgeTree }

@[simp]
def Graph.neighbor {G : Graph} : G.vertex → G.vertex → Bool :=
  fun u v =>
    lt_by_cases u v
      (fun u_lt_v => G.edgeTree.mem (Edge.mk v (Fin.mk u u_lt_v)))
      (fun _ => false)
      (fun v_lt_u => G.edgeTree.mem (Edge.mk u (Fin.mk v v_lt_u)))

lemma Graph.irreflexiveNeighbor (G : Graph) :
  ∀ (v : G.vertex), ¬ neighbor v v := by simp [lt_by_cases]

lemma Graph.symmetricNeighbor (G : Graph) :
  ∀ (u v : G.vertex), neighbor u v → neighbor v u := by
    intros u v
    cases lt_trichotomy u v with
    | inl u_lt_v => simp [lt_by_cases, not_lt_of_lt, u_lt_v]
    | inr h =>
      cases h with
      | inl u_eq_v => rw [u_eq_v] ; intro ; assumption
      | inr v_lt_u => simp [lt_by_cases, not_lt_of_lt, v_lt_u]
