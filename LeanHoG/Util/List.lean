import Mathlib.Tactic

namespace List

@[simp]
def all_distinct {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => x ∉ xs && xs.all_distinct

theorem all_distinct_iff_nodup {α : Type} [DecidableEq α] {l : List α} :
  l.all_distinct = true ↔ l.Nodup := by
  induction' l
  repeat simp_all

theorem all_distinct_iff_dedup {α : Type} [DecidableEq α] (l : List α) :
  l.all_distinct = true ↔ List.dedup l = l := by
  simp only [all_distinct_iff_nodup, List.dedup_eq_self]


theorem index_of_lt_length_of_exists {α : Type} [DecidableEq α] (xs : List α)
  (_ : xs.all_distinct) (x : α) (h : x ∈ xs) :
  xs.indexOf x < xs.length := by
  apply List.findIdx_lt_length_of_exists
  apply Exists.intro x
  apply And.intro
  exact h
  simp

lemma all_distinct_concat_iff_cons {α : Type} [DecidableEq α] {l : List α} {x : α} :
  (l ++ [x]).all_distinct ↔ (x :: l).all_distinct := by
  apply Iff.intro
  · intro h'
    induction' l with y ys ih
    simp
    aesop
  · intro h'
    induction' l with y ys ih
    simp
    aesop

lemma all_distinct_concat_singleton {α : Type} [DecidableEq α] {l : List α}
  {h : l.all_distinct} {x : α} :
  (l ++ [x]).all_distinct ↔ x ∉ l := by
  apply Iff.mpr (iff_congr all_distinct_concat_iff_cons (Iff.refl _))
  aesop

@[simp]
theorem all_distinct_injective_map {α β: Type} [DecidableEq α] [DecidableEq β]
  {l : List α} {h : l.all_distinct} {f : α → β} {inj : Function.Injective f} :
  (map f l).all_distinct := by
  induction' l with x xs ih
  · simp
  · simp
    apply And.intro
    · intros y y_nin_xs
      simp at h
      by_contra fx_eq_fy
      have x_eq_y : x = y := by aesop
      have x_nin_xs : x ∉ xs := h.1
      rw [x_eq_y] at x_nin_xs
      contradiction
    · simp at h
      apply ih
      exact h.2

-- TODO: Surely we can just apply the theorem we used to prove this instead of a separate theorem
theorem get_implies_get? {α : Type} {l : List α} {i j : Fin l.length} :
  (l.get i) = (l.get j) → l.get? i = l.get? j := by
  simp [List.get?_eq_get]

@[simp]
theorem all_distinct_get_injective {α : Type} [DecidableEq α] {l : List α} {h : l.all_distinct}
  {i j : Fin l.length} : l.get i = l.get j → i = j := by
  intro eq
  have H : l.Nodup := by apply Iff.mp all_distinct_iff_nodup h
  have : l.get? i = l.get? j := by apply get_implies_get? eq
  apply Iff.mp Fin.val_inj
  apply List.get?_injective (by apply i.isLt) H this

@[simp] theorem all_distinct_get_injective_function {α : Type} [DecidableEq α] {l : List α}
  {h : l.all_distinct} : Function.Injective (l.get) := by
  unfold Function.Injective
  intros _ _ h'
  apply all_distinct_get_injective h'
  exact h

lemma not_all_distinct_exists_duplicate {α : Type} [DecidableEq α] (l : List α)
  (h : ¬ l.all_distinct) :
  ∃ i j, i ≠ j ∧ l.get i = l.get j := by
  have h' : ¬ l.Nodup := by
    apply Iff.mp (not_congr all_distinct_iff_nodup)
    exact h
  have h''' : ¬ ∀ (i j : ℕ), i < j → j < List.length l → List.get? l i ≠ List.get? l j := by
    apply Iff.mp (not_congr List.nodup_iff_get?_ne_get?)
    exact h'
  simp at h'''
  let ⟨i, j, cond⟩ := h'''
  have i_lt : i < l.length := by linarith
  have j_lt : j < l.length := by linarith
  apply Exists.intro ⟨i, i_lt⟩
  apply Exists.intro ⟨j, j_lt⟩
  simp_all only [gt_iff_lt, get?_eq_get, Option.some.injEq, true_and, ne_eq, Fin.mk.injEq, and_true]
  unhygienic with_reducible aesop_destruct_products
  simp_all only [gt_iff_lt, get?_eq_get]
  apply Aesop.BuiltinRules.not_intro
  intro i_eq_j
  simp_all only [lt_self_iff_false]

/--
  Reformulation of injectivity of get for a list with the `all_distinct` property.
-/
theorem all_distinct_get_inj {α : Type} [DecidableEq α] (l : List α) (d : l.all_distinct = true) :
  (∀ (i j : Fin l.length), l.get i = l.get j → i = j) := by
  have d' : l.Nodup := Iff.mp all_distinct_iff_nodup d
  intros i j h
  let h' : l.get? i = l.get? j := get_implies_get? h
  have := List.get?_inj i.2 d' h'
  apply Fin.ext this -- have to apply Fin extensionality

/-- Given an element [x] of a list [l] and a proof that x ∈ l,
    produce the index of [x] in [l].
-/
def mem_to_idx {α : Type} [BEq α] [LawfulBEq α] (x : α) (l : List α) (h : x ∈ l) :
  (k : Fin l.length) ×' (l.get k = x) := by
  let boo : ∃ (y : α), (y ∈ l) ∧ (y == x) := by
    apply Exists.intro x
    apply And.intro
    exact h
    simp
  let foo := @List.findIdx_lt_length_of_exists α (· == x) l boo
  have bar : List.findIdx (· == x) l < l.length := by apply foo
  have moo := @List.findIdx_get α (· == x) l bar
  exact ⟨⟨List.findIdx (· == x) l, bar⟩, by aesop⟩

lemma length_gt_one_ne_singleton {α : Type} (l : List α) (h : 1 < l.length) :
  ∀ (x : α), l ≠ [x] := by
  intro x
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  aesop_subst a
  simp_all only [length_singleton, lt_self_iff_false]

lemma length_gt_exists_get {α : Type} [DecidableEq α] {l : List α} {i : Fin l.length} :
  ∃ (x : α), l.get i = x := by
  simp_all only [exists_eq']

@[simp]
lemma range_all_distinct {n : Nat} : (List.range n).all_distinct := by
  induction' n with n ih
  · simp
  · rw [List.range_succ]
    apply Iff.mpr all_distinct_concat_singleton
    apply List.not_mem_range_self
    exact ih

@[simp]
lemma range_nodup {n : Nat} : (List.range n).Nodup := by
  apply Iff.mp all_distinct_iff_nodup
  simp

lemma all_distinct_finRange_succ {n : Nat} : all_distinct (concat (map Fin.castSucc (finRange n)) (Fin.last n)) ↔
  all_distinct (Fin.last n :: (map Fin.castSucc (finRange n))) := by
  apply Iff.intro
  · intro h
    simp at h
    apply Iff.mp all_distinct_concat_iff_cons at h
    exact h
  · intro h
    simp
    apply Iff.mpr all_distinct_concat_iff_cons at h
    exact h

@[simp]
lemma finRange_all_distinct {n : Nat} : (List.finRange n).all_distinct := by
  induction' n with n ih
  · simp
  · rw [List.finRange_succ]
    apply Iff.mpr all_distinct_finRange_succ
    simp
    apply And.intro
    · intro k
      have : Fin.castSucc k < Fin.last n := Fin.castSucc_lt_last k
      aesop
    · apply all_distinct_injective_map
      exact ih
      exact (Fin.castSucc_injective n)

@[simp]
def finRange_get (n : Nat) : Fin n → Fin n :=
  fun i => (List.finRange n).get (Eq.symm (List.length_finRange n) ▸ i)

theorem finRange_get_inj {n : Nat} (i j : Fin n) :
  (finRange_get n) i = (finRange_get n) j → i = j := by
  intro h
  have := all_distinct_get_inj (List.finRange n) finRange_all_distinct
  have len : n = (List.finRange n).length := Eq.symm (List.length_finRange n)
  simp at h
  have := this (len ▸ i) (len ▸ j) h
  aesop

@[simp]
theorem finRange_get_injective {n : Nat} : Function.Injective (finRange_get n) := by
  unfold Function.Injective
  intros i j
  apply finRange_get_inj i j

@[simp]
theorem finRange_get_surjective {n : Nat} : Function.Surjective (finRange_get n) := by
  apply Function.Injective.surjective_of_fintype
  exact Equiv.refl (Fin n)
  apply finRange_get_injective

@[simp]
theorem finRange_get_bijective {n : Nat} : Function.Bijective (finRange_get n) := by
  unfold Function.Bijective
  exact ⟨finRange_get_injective, finRange_get_surjective⟩

/-- Maps indices of a list to the values in the list at those indices. -/
@[simp]
def list_to_fun {α : Type} (l : List α) : Fin l.length → { x : α // x ∈ l } :=
  fun i =>
    ⟨l.get i, List.get_mem l i.val i.isLt⟩

@[simp]
theorem list_to_fun_all_distinct_inj {α : Type} [DecidableEq α] {l : List α}
  {h : l.all_distinct} {i j : Fin l.length} :
  (list_to_fun l) i = (list_to_fun l) j → i = j := by
  intro eq
  have := all_distinct_get_inj l h
  simp at eq
  apply this i j eq

@[simp]
theorem list_to_fun_all_distinct_injective {α : Type} [DecidableEq α] (l : List α)
  (h : l.all_distinct) : Function.Injective (list_to_fun l) := by
  unfold Function.Injective
  intros i j
  apply list_to_fun_all_distinct_inj
  exact h

@[simp]
theorem list_to_fun_all_distinct_surjective {α : Type} [DecidableEq α] (l : List α)
  (h : l.all_distinct) : Function.Surjective (list_to_fun l) := by
  apply Function.Injective.surjective_of_fintype
  apply List.Nodup.getEquiv
  apply Iff.mp all_distinct_iff_nodup h
  apply list_to_fun_all_distinct_injective
  exact h

theorem list_to_fun_all_distinct_bijective {α : Type} [DecidableEq α] (l : List α)
  (h : l.all_distinct) : Function.Bijective (list_to_fun l) := by
  unfold Function.Bijective
  exact ⟨list_to_fun_all_distinct_injective l h, list_to_fun_all_distinct_surjective l h⟩

@[simp]
def finRange_to_finset (n : Nat) : Finset (Fin n) :=
  let range := List.finRange n
  range.toFinset

theorem all_distinct_list_get_inj {n : Nat} {l : List (Fin n)}
  {h : l.all_distinct} {i j : Fin l.length} :
  l.get i = l.get j → i = j := by
  intro eq
  have := all_distinct_get_inj l h
  apply this i j eq

theorem all_distinct_list_get_injective {n : Nat} {l : List (Fin n)}
  {h : l.all_distinct} : Function.Injective l.get := by
  unfold Function.Injective
  apply all_distinct_list_get_inj
  exact h

theorem all_distinct_list_get_surjective {n : Nat} {l : List (Fin n)} {len : n = l.length}
  {h : l.all_distinct} : Function.Surjective l.get := by
  apply Function.Injective.surjective_of_fintype
  rw [← len]
  apply all_distinct_list_get_injective
  exact h

theorem all_distinct_list_get_bijective {n : Nat} (l : List (Fin n)) (len : n = l.length)
  (h : l.all_distinct) : Function.Bijective l.get := by
  unfold Function.Bijective
  apply And.intro
  apply all_distinct_list_get_injective
  exact h
  apply all_distinct_list_get_surjective
  exact len
  exact h

-- This is just a corollary of surjectivity of get in this case
lemma all_distinct_exists_mem {n : Nat} {l : List (Fin n)} {len : n = l.length}
  {h : l.all_distinct} {i : Fin n} :
  ∃ (j : Fin l.length), l.get j = i := by
  have := @all_distinct_list_get_surjective n l len h
  let ⟨j, cond⟩ := this i
  apply Exists.intro j cond

end List
