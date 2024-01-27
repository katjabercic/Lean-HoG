import LeanSAT

namespace HoG

open LeanSAT Model

@[simp]
def disj_list {ν : Type} : List (PropForm ν) → PropForm ν
  | [] => PropForm.fls
  | p :: ps => PropForm.disj p (disj_list ps)

open PropForm in
lemma satisfies_disj_list {ν : Type} {τ : PropAssignment ν} {ps : List (PropForm ν)} :
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
def conj_list {ν : Type} : List (PropForm ν) → PropForm ν
  | [] => PropForm.tr
  | p :: ps => PropForm.conj p (conj_list ps)

open PropForm in
lemma satisfies_conj_list {ν : Type} {τ : PropAssignment ν} {ps : List (PropForm ν)} :
  τ ⊨ (conj_list ps) ↔ ∀ p ∈ ps, τ ⊨ p := by
  induction' ps with q qs ih
  repeat aesop

end HoG
