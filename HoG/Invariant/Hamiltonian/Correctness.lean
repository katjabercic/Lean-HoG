import Mathlib.Tactic.LibrarySearch

import HoG.Graph
import HoG.Invariant.EdgeSize
import HoG.Invariant.Hamiltonian.SatHelpers
import HoG.Util.List

import LeanSAT

namespace HoG

open LeanSAT Model PropForm

def piglet1 : Graph :=
  { vertexSize := 3,
    edgeTree := .node (Edge.mk 0 ⟨2, by simp⟩ (by norm_num)) (.leaf (Edge.mk 0 ⟨1, by simp⟩ (by norm_num))) (.leaf (Edge.mk 1 ⟨2, by simp⟩ (by norm_num)))
    edgeCorrect := by rfl
  }

@[simp, reducible] def Fin.coe {n k : Nat} {h : k < n} : Fin k → Fin n := fun i =>
  ⟨i, Nat.lt_trans i.isLt h⟩

@[simp, reducible]
def Pos (n : Nat) := (Fin n) × (Fin n)

def Pos.coe {n k : Nat} {h : k < n} : Pos k → Pos n := fun p =>
  (⟨p.1, Nat.lt_trans p.1.isLt h⟩,⟨p.2, Nat.lt_trans p.2.is_lt h⟩)

instance (n : Nat) : Repr (Pos n) where
  reprPrec p _ :=
    match n with
    | 0 => s!"()"
    | _+1 => s!"{p}"

abbrev x {n : Nat} (i j : Fin n) : PropForm (Pos n) := .var (i,j)

abbrev c {n : Nat} (i : Fin n) : PropForm (Pos n) :=
  let range := List.finRange n
  disj_list (range.map fun j => x j i)

@[simp] lemma satisfies_c_iff {n : Nat} {i : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ c i ↔ ∃ (j : Fin n), τ ⊨ x j i := by
  simp [satisfies_disj_list]

@[simp]
def satisfies_c_to_witness {n : Nat} {i : Fin n} {τ : PropAssignment (Pos n)}
  (h : τ ⊨ c i) : (j : Fin n) ×' τ ⊨ x j i := by
  let ⟨x_ji, ⟨p_in_list, τ_sat_p⟩⟩ := satisfies_disj_list_to_witness _ h
  let ⟨j, cond⟩ := List.mem_to_idx x_ji _ p_in_list
  simp [List.mem_map] at cond
  exact ⟨{ val := j.val, isLt := (_ : j.val < n) }, by rw [cond]; exact τ_sat_p⟩

abbrev at_least_one_at_pos (n : Nat) : PropForm (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => c i)

@[simp] lemma satisfies_at_least_one_at_pos_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_least_one_at_pos n ↔ ∀ (i : Fin n), τ ⊨ c i := by
  simp [satisfies_conj_list]

@[simp]
def satisfying_assignment_to_list {n : Nat} (τ : PropAssignment (Pos n))
  (h : τ ⊨ at_least_one_at_pos n) : List (Fin n) := by
  -- For each (i : Fin n), τ gives a (j : Fin), we set l[i] := j.
  -- Because of at_least_one_at_pos, this `j` is unique.
  apply Iff.mp satisfies_at_least_one_at_pos_iff at h
  have h' : ∀ (i : Fin n), (j : Fin n) ×' τ ⊨ x j i := by
    intro i
    apply satisfies_c_to_witness (h i)
  let range := List.finRange n
  let l := range.map (fun i => (h' i).fst)
  exact l

lemma satisfying_assignment_list_len {n : Nat} (τ : PropAssignment (Pos n))
  (h : τ ⊨ at_least_one_at_pos n) : n = (satisfying_assignment_to_list τ h).length := by
  simp [Pos, List.length_map, List.length_finRange]

open PropForm.Notation in
abbrev d {n : Nat} (j : Fin n) : PropForm (Pos n) :=
  let is := List.finRange n
  let ks := List.finRange n
  let pairs := is ×ˢ ks
  let distinct_pairs := List.filter (fun (i,k) => i ≠ k) pairs
  conj_list (distinct_pairs.map fun (i,k) => disj_list [neg (x i j), neg (x k j)])

@[simp] lemma satisfies_d_iff {n : Nat} {j : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ d j ↔ (∀ i k, i ≠ k → satisfies τ (neg (x i j)) ∨ satisfies τ (neg (x k j))) := by
  apply Iff.intro
  · intro h
    simp [satisfies_conj_list] at h
    intros i k i_neq_k
    have := h (disj_list [neg (x i j), neg (x k j)]) i k
    simp [List.mem_filter, i_neq_k] at this
    simp [this, PropForm.satisfies]
  · intro h
    simp [satisfies_conj_list]
    intros p i k i_k_in
    simp [List.mem_filter, List.mem_product] at i_k_in
    have := h i k i_k_in
    intro ass
    cases' this with h h
    · rw [← ass]
      simp [PropForm.satisfies_disj]
      apply Or.intro_left
      simp [PropForm.satisfies] at h
      assumption
    · rw [← ass]
      simp [PropForm.satisfies_disj]
      apply Or.intro_right
      simp [PropForm.satisfies] at h
      assumption

abbrev at_most_one_at_pos (n : Nat) : PropForm (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => d i)

@[simp] lemma satisfies_at_most_one_at_pos_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_most_one_at_pos n ↔ ∀ (j : Fin n), τ ⊨ d j := by
  simp [satisfies_conj_list]

open PropForm.Notation in
abbrev exactly_one_at_pos (n : Nat) : PropForm (Pos n) :=
  at_least_one_at_pos n ∧ at_most_one_at_pos n

example (n : Nat) : ∀ (k : Fin (n + 1)), k = n ∨ k ≠ n := by
  exact fun k => eq_or_ne k ↑n

lemma at_least_one_at_pos_succ {n : Nat} {τ : PropAssignment (Pos (n + 1))} :
  τ ⊨ at_least_one_at_pos (n+1) →
  ∀ (j : Fin (n+1)), (∃ (i : Fin n), τ ⊨ @x (n+1) i j) ∨ τ ⊨ x (Fin.last n) j := by
  intro h
  simp at h
  simp
  intro j
  have h := h j
  have ⟨i, cond⟩ := h
  have i_eq_n_or_lt := Fin.eq_castSucc_or_eq_last i
  cases' i_eq_n_or_lt with h' h'
  · let ⟨i', i'_eq_i⟩ := h'
    apply Or.intro_left
    apply Exists.intro i'
    rw [← i'_eq_i]
    exact cond
  · apply Or.intro_right
    rw [← h']
    exact cond

lemma fin_eq_coe {n : Nat} {i k : Fin n} : (i : Fin (n+1)) = (k : Fin (n+1)) → i = k := by
  intro h
  apply Iff.mp Fin.castSucc_inj
  simp_all only [Fin.coe_eq_castSucc]

lemma fin_neq_coe {n : Nat} {i k : Fin n} : i ≠ k → (i : Fin (n+1)) ≠ (k : Fin (n+1)) := by
  intro h
  by_contra h'
  suffices i = k from by contradiction
  apply Iff.mp Fin.castSucc_inj
  simp_all only [ne_eq, Fin.coe_eq_castSucc]

lemma at_most_one_at_pos_succ {n : Nat} {τ : PropAssignment (Pos (n + 1))} :
  τ ⊨ at_most_one_at_pos (n+1) →
  ∀ (j : Fin n), ∀ (i k : Fin n), i ≠ k →
    (τ ⊨ neg (@x (n+1) i j)) ∨ (τ ⊨ neg (@x (n+1) k j)) := by
  intros h j i k i_neq_k
  simp at h
  apply h j i k (fin_neq_coe i_neq_k)

lemma list_exists_get {α : Type} {xs : List α} {n : Fin xs.length} :
  ∃ (x : α), xs.get n = x := by
  exact exists_eq'

lemma list_forall_exists_get {α : Type} {xs : List α} :
  ∀ (i : Fin xs.length), ∃ (x : α) , xs.get i = x := by
  intro i
  exact exists_eq'

example (α : Type) (P Q : α → Prop) (h : ∀ x, (P x ↔ Q x)) : (∀ x, P x) ↔ (∀x, Q x) := by
  exact forall_congr' h

lemma satisfies_neg_neg {ν : Type} {τ : PropAssignment ν} (p : PropForm ν) :
  τ ⊨ p ↔ τ ⊨ neg (neg p) := by
  simp only [satisfies_neg, not_not]

#check PropForm.satisfies_neg

lemma satisfies_neg_or {ν : Type} {τ : PropAssignment ν} {p q : PropForm ν} :
  ¬(τ ⊨ (neg p) ∨ τ ⊨ (neg q)) ↔ τ ⊨ p ∧ τ ⊨ q := by
  simp_all only [satisfies_neg, not_or, not_not]

theorem list_to_satisfying_assignment {n : Nat} :
  (∃ (l : List (Fin n)), l.length = n)  →
  (∃ (τ : PropAssignment (Pos n)), τ ⊨ exactly_one_at_pos n) := by
  intro h
  let ⟨l, l_len⟩ := h
  let q : Fin n = Fin l.length := by rw [l_len]
  let τ : PropAssignment (Pos n) := fun pos =>
    match pos with
    | (i,j) => if l.get (q▸j) = i then true else false
  apply Exists.intro τ
  apply Iff.mpr PropForm.satisfies_conj
  apply And.intro
  · have : τ ⊨ at_least_one_at_pos n ↔ ∀ (i : Fin n), τ ⊨ c i := by
      simp [satisfies_conj_list]
    apply Iff.mpr this
    have : ∀ (i : Fin n), (τ ⊨ c i ↔ ∃ (j : Fin n), τ ⊨ x j i) := by
      simp [satisfies_disj_list]
    apply Iff.mpr (forall_congr' this)
    have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (q▸i) = j) := by
      intros i j
      apply Iff.intro
      · intro t_xji
        simp at t_xji
        by_contra neg
        apply t_xji neg
      aesop
    suffices ∀ i, ∃ j, l.get (q▸i) = j by aesop
    aesop
  · apply Iff.mpr satisfies_at_most_one_at_pos_iff
    intro j
    apply Iff.mpr satisfies_d_iff
    intros i k i_neq_k
    by_contra h
    have : satisfies τ (x i j) ∧ satisfies τ (x k j) := by
      apply Iff.mp satisfies_neg_or h
    have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (q▸i) = j) := by
      intros i j
      apply Iff.intro
      · intro t_xji
        simp at t_xji
        by_contra neg
        apply t_xji neg
      aesop
    have l_at_j_eq_i : l.get (q▸j) = i := by
      apply Iff.mp (x_i_j_def j i)
      exact this.1
    have l_at_j_eq_k : l.get (q▸j) = k := by
      apply Iff.mp (x_i_j_def j k)
      exact this.2
    have : i = k := by
      rw [← l_at_j_eq_i, ← l_at_j_eq_k]
    contradiction

theorem list_iff_satisfiying_assignemnt {n : Nat} :
  (∃ (l : List (Fin n)), l.length = n) ↔
  (∃ (τ : PropAssignment (Pos n)), τ ⊨ exactly_one_at_pos n) := by
  apply Iff.intro
  apply list_to_satisfying_assignment
  sorry

abbrev a {n : Nat} (i : Fin n) : PropForm (Pos n) :=
  let range := List.finRange n
  disj_list (range.map fun j => x i j)

open PropForm.Notation in
abbrev b {n : Nat} (i : Fin n) : PropForm (Pos n) :=
  let js := List.finRange n
  let ks := List.finRange n
  let pairs := js ×ˢ ks
  let distinct_pairs := List.filter (fun (j,k) => j ≠ k) pairs
  conj_list (distinct_pairs.map fun (j,k) => disj_list [¬x i j, ¬x i k])

abbrev at_least_one_fin_n (n : Nat) : PropForm (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => a i)

abbrev at_most_one_fin_n (n : Nat) : PropForm (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => b i)

open PropForm.Notation in
abbrev exactly_one_fin_n (n : Nat) : PropForm (Pos n) :=
  at_least_one_fin_n n ∧ at_most_one_fin_n n

open PropForm.Notation in
abbrev exactly_one (n : Nat) :=
  exactly_one_at_pos n ∧ exactly_one_fin_n n

@[simp]
def satisfying_assignment_to_all_distinct_list {n : Nat} (τ : PropAssignment (Pos n))
  (h : τ ⊨ exactly_one n) : (l : List (Fin n)) ×' (l.length = n ∧ l.all_distinct) := by
  -- For each (i : Fin n), τ gives a (j : Fin), we set l[i] := j.
  -- Because of at_least_one_at_pos, this `j` is unique.
  apply Iff.mp PropForm.satisfies_conj at h
  have h_exactly_one_at_pos := h.1
  have h_exactly_one_n := h.2
  apply Iff.mp PropForm.satisfies_conj at h_exactly_one_at_pos
  have h_at_least_one_at_pos := h_exactly_one_at_pos.1
  have h_at_most_one_at_pos := h_exactly_one_at_pos.2
  apply Iff.mp satisfies_at_least_one_at_pos_iff at h_at_least_one_at_pos
  have h' : ∀ (i : Fin n), (j : Fin n) ×' τ ⊨ x j i := by
    intro i
    apply satisfies_c_to_witness (h_at_least_one_at_pos i)
  let range := List.finRange n
  let l := range.map (fun i => (h' i).fst)
  have len : l.length = n := by simp
  have l_all_distinct : l.all_distinct := by
    by_contra not_all_distinct
    sorry
  sorry

lemma satisfying_assignment_to_bijection {n : Nat}
  (l : List (Fin n)) (len : l.length = n) (l_distinct : l.all_distinct) :
  (τ : PropAssignment (Pos n)) ×' τ ⊨ exactly_one n := by
  sorry


end HoG
