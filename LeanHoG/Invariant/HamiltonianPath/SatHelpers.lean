import LeanSAT

namespace LeanHoG
namespace PropFun

open LeanSAT Model PropFun

@[simp]
def disj_list {ν : Type} : List (PropFun ν) → PropFun ν
  | [] => PropFun.fls
  | p :: ps => p ⊔ (disj_list ps)

def satisfies_disj_list_to_witness {ν : Type} {τ : PropAssignment ν} (ps : List (PropFun ν))
  (h : τ ⊨ (disj_list ps)) : (p : PropFun ν) ×' (p ∈ ps ∧ τ ⊨ p) :=
  match ps with
  | [] => by contradiction
  | p :: ps => by
    simp at h
    if τ_sat_p : τ ⊨ p then
      exact ⟨p, ⟨List.mem_cons_self _ _, τ_sat_p⟩⟩
    else
      simp [τ_sat_p] at h
      let ⟨p', ⟨p'_mem, τ_sat_p'⟩⟩ := satisfies_disj_list_to_witness ps h
      exact ⟨p', ⟨List.mem_cons_of_mem p p'_mem, τ_sat_p'⟩⟩

lemma satisfies_disj_list {ν : Type} {τ : PropAssignment ν} {ps : List (PropFun ν)} :
  τ ⊨ (disj_list ps) ↔ ∃ p ∈ ps, τ ⊨ p := by
  apply Iff.intro
  · intro h
    induction' ps with p ps ih
    · contradiction
    · simp at h
      cases' h with h h
      · apply Exists.intro p
        simp
        assumption
      · have := ih h
        let ⟨p, p_in_ps, sat⟩ := this
        apply Exists.intro p
        simp [p_in_ps]
        assumption
  · intro h
    induction' ps with q qs ih
    · let ⟨p, _, _⟩ := h
      contradiction
    · let ⟨p, p_in_ps, sat⟩ := h
      simp
      simp at p_in_ps
      cases' p_in_ps with p_eq_q
      · apply Or.intro_left
        rw [← p_eq_q]
        assumption
      · apply Or.intro_right
        apply ih
        apply Exists.intro p
        apply And.intro
        assumption
        assumption

@[simp]
def conj_list {ν : Type} : List (PropFun ν) → PropFun ν
  | [] => PropFun.tr
  | p :: ps => p ⊓ (conj_list ps)

lemma satisfies_conj_list {ν : Type} {τ : PropAssignment ν} {ps : List (PropFun ν)} :
  τ ⊨ (conj_list ps) ↔ ∀ p ∈ ps, τ ⊨ p := by
  induction' ps with q qs ih
  simp_all only [conj_list, satisfies_tr, List.find?_nil, List.not_mem_nil, IsEmpty.forall_iff, forall_const]
  · simp
    rfl
  · simp_all [conj_list, satisfies_conj, List.mem_cons, forall_eq_or_imp]

lemma satisfies_disj_fls {ν : Type} {τ : PropAssignment ν} {p : PropFun ν} :
  τ ⊨ p ⊔ fls ↔ τ ⊨ p := by
  apply Iff.intro
  · intro h
    simp at h
    cases' h with h h'
    exact h
    contradiction
  · intro h
    simp
    apply Or.intro_left
    exact h

lemma satisfies_neg_or {ν : Type} {τ : PropAssignment ν} {p q : PropFun ν} :
  ¬ (τ ⊨ pᶜ ∨ τ ⊨ qᶜ) ↔ τ ⊨ p ∧ τ ⊨ q := by
  simp [not_or]

lemma not_or_satisfies_not {ν : Type} {τ : PropAssignment ν} {φ₁ φ₂ : PropFun ν} :
  ¬ (τ ⊨ φ₁ᶜ ∨ τ ⊨ φ₂ᶜ) ↔ τ ⊨ φ₁ ∧ τ ⊨ φ₂ := by
  apply Iff.intro
  · intro h
    simp_all only [satisfies_neg, not_not, and_self, not_or]
  · intro h
    simp_all only [satisfies_neg, not_true_eq_false, or_self, not_false_eq_true]

end PropFun
end LeanHoG
