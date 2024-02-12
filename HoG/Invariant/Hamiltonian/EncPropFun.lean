import Mathlib.Tactic.LibrarySearch

import HoG.Graph
import HoG.Invariant.EdgeSize
import HoG.Invariant.Hamiltonian.Definition
import HoG.Invariant.Hamiltonian.SatHelpersPropFun
import HoG.Invariant.Hamiltonian.SatHelpers
import HoG.Util.List

import LeanSAT

namespace HoG

open LeanSAT Model PropFun

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

abbrev x {n : Nat} (i j : Fin n) : PropFun (Pos n) := .var (i,j)

abbrev a {n : Nat} (i : Fin n) : PropFun (Pos n) :=
  let range := List.finRange n
  disj_list (range.map fun j => x i j)

abbrev b {n : Nat} (i : Fin n) : PropFun (Pos n) :=
  let js := List.finRange n
  let ks := List.finRange n
  let pairs := js ×ˢ ks
  let distinct_pairs := List.filter (fun (j,k) => j ≠ k) pairs
  conj_list (distinct_pairs.map fun (j,k) => disj_list [(x i j)ᶜ, (x i k)ᶜ])

abbrev c {n : Nat} (i : Fin n) : PropFun (Pos n) :=
  let range := List.finRange n
  disj_list (range.map fun j => x j i)

abbrev d {n : Nat} (j : Fin n) : PropFun (Pos n) :=
  let is := List.finRange n
  let ks := List.finRange n
  let pairs := is ×ˢ ks
  let distinct_pairs := List.filter (fun (i,k) => i ≠ k) pairs
  conj_list (distinct_pairs.map fun (i,k) => disj_list [(x i j)ᶜ, (x k j)ᶜ])

abbrev e {g : Graph} (k k' : Fin g.vertexSize) :
  PropFun (Pos g.vertexSize) :=
  let n := g.vertexSize
  let is := List.finRange n
  let js := List.finRange n
  let pairs := is ×ˢ js
  let non_edges := List.filter (fun (i,j) => ¬ (g.badjacent i j)) pairs
  conj_list (non_edges |>.map fun (i,j) => disj_list [(x i k)ᶜ, (x j k')ᶜ])

@[simp] lemma satisfies_a_iff {n : Nat} {i : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ a i ↔ ∃ (j : Fin n), τ ⊨ x i j := by
  simp [satisfies_disj_list]

@[simp] lemma satisfies_b_iff {n : Nat} {i : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ b i ↔ (∀ j k, j ≠ k → τ ⊨ (x i j)ᶜ ∨ τ ⊨ (x i k)ᶜ) := by
  apply Iff.intro
  · intro h
    simp [satisfies_conj_list] at h
    intros j k j_neq_k
    have := h (disj_list [(x i j)ᶜ, (x i k)ᶜ]) j k
    simp [List.mem_filter, j_neq_k] at this
    simp [this]
    have not_sat_fls : τ ⊭ fls := by apply not_satisfies_fls
    simp [not_sat_fls] at this
    exact this
  · intro h
    simp [satisfies_conj_list]
    intros p j k j_k_in
    simp [List.mem_filter, List.mem_product] at j_k_in
    have := h j k j_k_in
    intro ass
    cases' this with h h
    · rw [← ass]
      apply Iff.mpr PropFun.satisfies_disj
      apply Or.intro_left
      exact h
    · rw [← ass]
      apply Iff.mpr PropFun.satisfies_disj
      apply Or.intro_right
      apply Iff.mpr PropFun.satisfies_disj_fls
      exact h

@[simp] lemma satisfies_c_iff {n : Nat} {i : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ c i ↔ ∃ (j : Fin n), τ ⊨ x j i := by
  simp [satisfies_disj_list]

@[simp] lemma satisfies_d_iff {n : Nat} {j : Fin n} {τ : PropAssignment (Pos n)} :
  τ ⊨ d j ↔ (∀ i k, i ≠ k → τ ⊨ (x i j)ᶜ ∨ τ ⊨ (x k j)ᶜ) := by
  apply Iff.intro
  · intro h
    simp [satisfies_conj_list] at h
    intros i k i_neq_k
    have := h (disj_list [(x i j)ᶜ, (x k j)ᶜ]) i k
    simp [List.mem_filter, i_neq_k] at this
    simp [this]
    have not_sat_fls : τ ⊭ fls := by apply not_satisfies_fls
    simp [not_sat_fls] at this
    exact this
  · intro h
    simp [satisfies_conj_list]
    intros p i k i_k_in
    simp [List.mem_filter, List.mem_product] at i_k_in
    have := h i k i_k_in
    intro ass
    cases' this with h h
    · rw [← ass]
      apply Iff.mpr PropFun.satisfies_disj
      apply Or.intro_left
      exact h
    · rw [← ass]
      apply Iff.mpr PropFun.satisfies_disj
      apply Or.intro_right
      apply Iff.mpr PropFun.satisfies_disj_fls
      exact h

@[simp] lemma satisfies_e_iff {g : Graph} {k k' : Fin g.vertexSize}
  {τ : PropAssignment (Pos g.vertexSize)} :
  τ ⊨ e k k' ↔ ∀ i j, ¬ g.badjacent i j → τ ⊨ (x i k)ᶜ ∨ τ ⊨ (x j k')ᶜ := by
  apply Iff.intro
  · intros h i j not_edge
    simp [satisfies_conj_list] at h
    have := h (disj_list [(x i k)ᶜ, (x j k')ᶜ]) i j
    simp [List.mem_filter, not_edge] at this
    simp [this]
    have not_sat_fls : τ ⊭ fls := by apply not_satisfies_fls
    simp [not_sat_fls] at this
    exact this
  · intro h
    simp [satisfies_conj_list]
    intros p i j not_edge
    simp [List.mem_filter] at h
    simp [List.mem_filter] at not_edge
    have := h i j not_edge
    intro ass
    cases' this with h h
    · rw [← ass]
      aesop_subst ass
      simp_all only [ge_iff_le, sup_le_iff, compl_le_compl_iff_le, satisfies_disj, Pos, satisfies_neg, satisfies_var,
        not_false_eq_true, Bool.not_eq_true, true_or]
    · rw [← ass]
      aesop_subst ass
      simp_all only [ge_iff_le, sup_le_iff, compl_le_compl_iff_le, satisfies_disj, Pos, satisfies_neg, satisfies_var,
        Bool.not_eq_true, not_false_eq_true, true_or, or_true]

abbrev at_least_one_at_pos (n : Nat) : PropFun (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => c i)

abbrev at_most_one_at_pos (n : Nat) : PropFun (Pos n) :=
  let range := List.finRange n
  conj_list (range.map fun i => d i)

abbrev exactly_one_at_pos (n : Nat) :=
  at_least_one_at_pos n ⊓ at_most_one_at_pos n

abbrev at_least_one_fin_n (n : Nat) :=
  let range := List.finRange n
  conj_list (range.map fun i => a i)

abbrev at_most_one_fin_n (n : Nat) :=
  let range := List.finRange n
  conj_list (range.map fun i => b i)

abbrev exactly_one_fin_n (n : Nat) :=
  at_least_one_fin_n n ⊓ at_most_one_fin_n n

abbrev exactly_one (n : Nat) :=
  exactly_one_at_pos n ⊓ exactly_one_fin_n n

abbrev no_non_edges (g : Graph) :=
  let ks := List.finRange g.vertexSize
  let pairs := ks ×ˢ ks
  let pairs := pairs.filter fun (k,k') => k.val + 1 = k'.val
  conj_list (pairs.map fun (k, k') => e k k')

@[simp] lemma satisfies_at_least_one_fin_n_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_least_one_fin_n n ↔ ∀ (i : Fin n), τ ⊨ a i := by
  simp [satisfies_conj_list]

@[simp] lemma satisfies_at_most_one_fin_n_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_most_one_fin_n n ↔ ∀ (j : Fin n), τ ⊨ b j := by
  simp [satisfies_conj_list]

@[simp] lemma satisfies_at_least_one_at_pos_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_least_one_at_pos n ↔ ∀ (i : Fin n), τ ⊨ c i := by
  simp [satisfies_conj_list]

@[simp] lemma satisfies_at_most_one_at_pos_iff {n : Nat} {τ : PropAssignment (Pos n)} :
  τ ⊨ at_most_one_at_pos n ↔ ∀ (j : Fin n), τ ⊨ d j := by
  simp [satisfies_conj_list]

@[simp] lemma satisfies_no_non_edges_iff {g : Graph} {τ : PropAssignment (Pos g.vertexSize)} :
  τ ⊨ no_non_edges g ↔
  ∀ (k k' : Fin g.vertexSize), k.val + 1 =  k'.val → τ ⊨ e k k' := by
  apply Iff.intro
  · intros h k k' rel
    simp [satisfies_conj_list, List.mem_filter] at h
    exact h (e k k') k k' rel rfl
  · intro h
    simp [satisfies_conj_list, List.mem_filter]
    intro p x x_1 a a_1
    aesop_subst a_1
    simp_all only [satisfies_e_iff, Bool.not_eq_true, satisfies_neg, satisfies_var, implies_true]

-- @[simp] def distinct_list_to_exactly_one_pos {n : Nat} (l : List (Fin n)) (l_len : n = l.length)
--   (_ : l.all_distinct) :
--   (τ : PropAssignment (Pos n)) ×' τ ⊨ exactly_one_at_pos n := by
--   let τ : PropAssignment (Pos n) := fun pos =>
--     match pos with
--     | (i,j) => if l.get (l_len ▸ j) = i then true else false
--   have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (l_len▸i) = j) := by
--     intros i j
--     apply Iff.intro
--     · intro t_xji
--       simp at t_xji
--       by_contra neg
--       apply t_xji neg
--     · aesop
--   have τ_sat_at_least : τ ⊨ at_least_one_at_pos n := by
--     apply Iff.mpr satisfies_at_least_one_at_pos_iff
--     suffices ∀ i, ∃ j, l.get (l_len▸i) = j by aesop
--     aesop
--   have τ_sat_at_most : τ ⊨ at_most_one_at_pos n := by
--     apply Iff.mpr satisfies_at_most_one_at_pos_iff
--     intro j
--     apply Iff.mpr satisfies_d_iff
--     aesop?
--     by_contra h
--     apply Iff.mp not_or at h
--     simp at h
--     let ⟨left, right⟩ := h
--     rw [left] at right
--     contradiction
--   have τ_sat : τ ⊨ exactly_one_at_pos n := by
--     apply Iff.mpr PropFun.satisfies_conj
--     exact ⟨τ_sat_at_least, τ_sat_at_most⟩
--   exact ⟨τ, τ_sat⟩

lemma helper {ν : Type} {φ₁ φ₂ : PropFun ν} {τ : PropAssignment ν} :
  ¬ (τ ⊨ φ₁ᶜ ∨ τ ⊨ φ₂ᶜ) ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  apply Iff.intro
  · intro h
    simp_all only [satisfies_neg, not_not, and_self, not_or]
  · intro h
    simp_all only [satisfies_neg, not_true_eq_false, or_self, not_false_eq_true]

-- @[simp] def distinct_list_to_exactly_one_fin_n {n : Nat} (l : List (Fin n)) (l_len : n = l.length)
--   (dist : l.all_distinct) :
--   (τ : PropAssignment (Pos n)) ×' τ ⊨ exactly_one_fin_n n := by
--   let τ : PropAssignment (Pos n) := fun pos =>
--     match pos with
--     | (i,j) => if l.get (l_len ▸ j) = i then true else false
--   have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (l_len▸i) = j) := by
--     intros i j
--     apply Iff.intro
--     · intro t_xji
--       simp at t_xji
--       by_contra neg
--       apply t_xji neg
--     · aesop
--   have τ_sat_at_least : τ ⊨ at_least_one_fin_n n := by
--     apply Iff.mpr satisfies_at_least_one_fin_n_iff
--     intro i
--     apply Iff.mpr satisfies_a_iff
--     suffices ∃ j, l.get (l_len ▸ j) = i from
--       by simp_all only [satisfies_var, ite_eq_left_iff]
--     -- XXX: Why doesn't this work
--     have := @List.all_distinct_exists_mem n l l_len dist i
--     let ⟨j, cond⟩ := this
--     apply Exists.intro (l_len ▸ j)
--     sorry

--   have τ_sat_at_most : τ ⊨ at_most_one_fin_n n := by
--     apply Iff.mpr satisfies_at_most_one_fin_n_iff
--     intro i
--     apply Iff.mpr satisfies_b_iff
--     intros j k j_neq_k
--     by_contra h
--     apply Iff.mp helper at h
--     let ⟨h₁, h₂⟩ := h
--     have h₁' : l.get (l_len ▸ j) = i := by
--       simp_all only [h₁]
--     have h₂' : l.get (l_len ▸ k) = i := by simp_all only [h₂]
--     have foo : (l_len ▸ j) = (l_len ▸ k) := by
--       apply List.all_distinct_list_get_inj
--       exact dist
--       rw [h₁', h₂']
--     have H : Fin n = Fin l.length := by simp [l_len]
--     have j_eq_k : j = k := by
--       apply Iff.mp (cast_inj H)
--       aesop_subst h₁'
--       simp_all only [Pos, List.list_to_fun, satisfies_var, ite_eq_left_iff, satisfies_at_least_one_fin_n_iff,
--         satisfies_a_iff, ne_eq, eq_rec_inj]
--     contradiction
--   have τ_sat : τ ⊨ exactly_one_fin_n n := by
--     apply Iff.mpr PropFun.satisfies_conj
--     exact ⟨τ_sat_at_least, τ_sat_at_most⟩
--   exact ⟨τ, τ_sat⟩

lemma get_subst {X : Type} {n : Nat} {l : List X} {l_len : n = l.length} {i : X}
  {h : ∃ j, l.get j = i} : ∃ j, l.get (l_len ▸ j) = i := by
  subst l_len
  simp [h]

lemma helper' {n : Nat} {l : List (Fin n)} {l_len : n = l.length} {i : Fin n}
  {h : ∃ j, l.get j = i} : ∃ j, l.get (l_len ▸ j) = i := by
  apply get_subst
  exact h

-- set_option maxHeartbeats 800000
-- lemma distinct_list_to_exactly_one {n : Nat} (l : List (Fin n)) (l_len : n = l.length)
--   (h : l.all_distinct) :
--   ∃ (τ : PropAssignment (Pos n)), τ ⊨ exactly_one n := by
--   let τ : PropAssignment (Pos n) := fun pos =>
--     match pos with
--     | (i,j) => if l.get (l_len ▸ j) = i then true else false
--   have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (l_len▸i) = j) := by
--     intros i j
--     apply Iff.intro
--     · intro t_xji
--       simp at t_xji
--       by_contra neg
--       apply t_xji neg
--     · aesop
--   have τ_sat_at_least_at_pos : τ ⊨ at_least_one_at_pos n := by
--     apply Iff.mpr satisfies_at_least_one_at_pos_iff
--     suffices ∀ i, ∃ j, l.get (l_len▸i) = j by aesop
--     aesop

--   have τ_sat_at_most_at_pos : τ ⊨ at_most_one_at_pos n := by
--     apply Iff.mpr satisfies_at_most_one_at_pos_iff
--     intro j
--     apply Iff.mpr satisfies_d_iff
--     aesop?
--     by_contra h
--     apply Iff.mp not_or at h
--     simp at h
--     let ⟨left, right⟩ := h
--     rw [left] at right
--     contradiction
--   have τ_sat_at_pos : τ ⊨ exactly_one_at_pos n := by
--     apply Iff.mpr PropFun.satisfies_conj
--     exact ⟨τ_sat_at_least_at_pos, τ_sat_at_most_at_pos⟩

--   have τ_sat_at_least_fin_n : τ ⊨ at_least_one_fin_n n := by
--     apply Iff.mpr satisfies_at_least_one_fin_n_iff
--     intro i
--     apply Iff.mpr satisfies_a_iff
--     suffices ∃ j, l.get (l_len ▸ j) = i from
--       by simp_all only [satisfies_var, ite_eq_left_iff]
--     have := @List.all_distinct_exists_mem n l l_len h i
--     apply helper'
--     exact this

--   have τ_sat_at_most_fin_n : τ ⊨ at_most_one_fin_n n := by
--     apply Iff.mpr satisfies_at_most_one_fin_n_iff
--     intro i
--     apply Iff.mpr satisfies_b_iff
--     intros j k j_neq_k
--     by_contra h'
--     apply Iff.mp helper at h'
--     let ⟨h₁, h₂⟩ := h'
--     have h₁' : l.get (l_len ▸ j) = i := by
--       simp_all only [h₁]
--     have h₂' : l.get (l_len ▸ k) = i := by
--       simp_all only [h₂]
--     have foo : (l_len ▸ j) = (l_len ▸ k) := by
--       apply List.all_distinct_list_get_inj
--       exact h
--       rw [h₁', h₂']
--     have H : Fin n = Fin l.length := by simp [l_len]
--     have j_eq_k : j = k := by
--       apply Iff.mp (cast_inj H)
--       aesop_subst h₁'
--       simp_all only [Pos, List.list_to_fun, satisfies_var, ite_eq_left_iff, satisfies_at_least_one_fin_n_iff,
--         satisfies_a_iff, ne_eq, eq_rec_inj]
--     contradiction

--   have τ_sat_fin_n : τ ⊨ exactly_one_fin_n n := by
--     apply Iff.mpr PropFun.satisfies_conj
--     exact ⟨τ_sat_at_least_fin_n, τ_sat_at_most_fin_n⟩

--   apply Exists.intro τ
--   apply Iff.mpr PropFun.satisfies_conj
--   exact ⟨τ_sat_at_pos, τ_sat_fin_n⟩

theorem hamiltonian_path_to_sat (g : Graph) (u v : g.vertex)
  (hp : HamiltonianPath u v) :
  ∃ (τ : PropAssignment (Pos g.vertexSize)), τ ⊨ no_non_edges g := by
  let n := g.vertexSize
  let l := hp.path.walk.vertices
  have h : l.all_distinct := by apply hp.path.isPath
  have l_len : n = l.length := by
    apply Eq.symm HamiltonianPath.length_eq_num_vertices
  let τ : PropAssignment (Pos n) := fun pos =>
    match pos with
    | (i,j) => if l.get (Fin.cast l_len j) = i then true else false
  have x_i_j_def : ∀ i j, (τ ⊨ x j i ↔ l.get (Fin.cast l_len i) = j) := by
    intros i j
    apply Iff.intro
    · intro t_xji
      simp at t_xji
      by_contra neg
      simp_all only [HamiltonianPath.vertices, Path.vertices, List.list_to_fun, ite_false]
    · aesop
  apply Exists.intro τ
  apply Iff.mpr satisfies_no_non_edges_iff
  intros k k' k_rel_k'
  apply Iff.mpr satisfies_e_iff
  intros i j non_edge_i_j
  have h₁ : τ ⊨ (x i k) ↔ List.get l (Fin.cast l_len k) = i := x_i_j_def k i
  have h₂ : τ ⊨ (x j k') ↔ List.get l (Fin.cast l_len k') = j := x_i_j_def k' j
  by_contra neg
  apply Iff.mp satisfies_neg_or at neg
  apply Iff.mp (Iff.and h₁ h₂) at neg
  have cast : g.vertexSize = hp.path.walk.vertices.length := by
    rw [← HamiltonianPath.length_eq_num_vertices]
    rfl
  have i_adj_j := @Path.consecutive_vertices_adjacent g u v hp.path.walk (Fin.cast cast k) (Fin.cast cast k') k_rel_k'
  have eq₁ := neg.1
  have eq₂ := neg.2
  have that : Graph.adjacent (l.get (Fin.cast l_len k)) (l.get (Fin.cast l_len k')) := by
    simp [i_adj_j]
  rw [eq₁, eq₂] at that
  simp [Graph.adjacent] at that
  contradiction

end HoG
