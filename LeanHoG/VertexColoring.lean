import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

structure VertexColoring (Color : Type) [DecidableEq Color] (G : Graph) : Type where
  color : G.vertex → Color
  colorCorrect :  ∀ (e : G.edge), color e.val.fst ≠ color e.val.snd

namespace VertexColoring

lemma adjacent_impl_color_ne {Color : Type} (G : Graph) [DecidableEq Color] (c : VertexColoring Color G) (u v : G.vertex) : G.adjacent u v → c.color u ≠ c.color v := by
  apply ltByCases u v
  · intro u_lt_v adj_u_v
    let edge_u_v := Graph.adjacentEdge adj_u_v
    have edge_u_v_adj : edge_u_v = Graph.adjacentEdge adj_u_v := by rfl
    have exists_edge := Graph.adj_impl_ex_edge G u v edge_u_v adj_u_v u_lt_v edge_u_v_adj
    obtain ⟨fst_eq_u, snd_eq_v⟩ := exists_edge
    rw [← fst_eq_u, ← snd_eq_v]
    apply (c.colorCorrect edge_u_v)
  · intro u_eq_v
    rw [u_eq_v]
    simp
    apply G.irreflexiveAdjacent
  · intro v_lt_u adj_v_u
    apply GT.gt.lt at v_lt_u
    apply G.symmetricAdjacent at adj_v_u
    let edge_v_u := Graph.adjacentEdge adj_v_u
    have edge_v_u_adj : edge_v_u = Graph.adjacentEdge adj_v_u := by rfl
    have exists_edge := Graph.adj_impl_ex_edge G v u edge_v_u adj_v_u v_lt_u edge_v_u_adj
    obtain ⟨snd_eq_u, fst_eq_v⟩ := exists_edge
    rw [← snd_eq_u, ← fst_eq_v]
    symm
    apply (c.colorCorrect edge_v_u)

/-TODO: Rename this. I lacked imagination...-/
lemma fin_2_ne_c_impl_eq (a b c : Fin 2) : a ≠ c → b ≠ c → a = b := by
  intro a_ne_b b_ne_c
  have c_le_1 : c ≤ 1 := by
    apply Fin.le_last
  apply Nat.lt_or_eq_of_le at c_le_1
  cases c_le_1 with
  | inl c_lt_1 =>
    simp at c_lt_1
    rw [← Fin.val_zero, Fin.val_eq_val c 0] at c_lt_1
    rw [c_lt_1] at a_ne_b
    rw [c_lt_1] at b_ne_c
    apply Fin.eq_one_of_neq_zero at a_ne_b
    apply Fin.eq_one_of_neq_zero at b_ne_c
    rw [a_ne_b, b_ne_c]
  | inr c_eq_1 =>
    simp at c_eq_1
    rw [← Fin.val_one, Fin.val_eq_val c 1] at c_eq_1
    rw [c_eq_1] at a_ne_b
    rw [c_eq_1] at b_ne_c
    have v_eq_zero (v : Fin 2) : v ≠ 1 → v = 0 := by
      intro v_neq
      rw [← Fin.val_ne_iff] at v_neq
      have le_1 : v.val ≤ 1 := by
        apply Fin.le_last
      have lt_1 : v.val < 1 := Ne.lt_of_le v_neq le_1
      rw [Nat.lt_one_iff, ← Fin.val_zero, Fin.val_eq_val] at lt_1
      assumption
    apply v_eq_zero at a_ne_b
    apply v_eq_zero at b_ne_c
    rw [a_ne_b, b_ne_c]

lemma EvenOddWalkEndpointEquality
  {G : Graph}
  {vₛ vₜ : G.vertex}
  (w : Walk G vₛ vₜ)
  (p : VertexColoring (Fin 2) G) :
  (Odd w.length → p.color vₛ ≠ p.color vₜ) ∧
  (Even w.length → p.color vₛ = p.color vₜ)
  := by
  induction w with
  | trivial s =>
    apply And.intro
    · intro H
      cases H with
      | intro k eq =>
        simp [Walk.length, Even, Odd] at eq
        contradiction
    · intro
      rfl
  | @left vₛ vᵤ vₜ adj_vₛ_vᵤ walk_vᵤ_vₜ ih =>
    apply And.intro
    · intro H
      cases H with
      | intro k eq =>
        simp [Walk.length, Even, Odd] at eq
        have wEv : Even walk_vᵤ_vₜ.length := by simp [eq]
        rw [← ih.right wEv]
        exact adjacent_impl_color_ne G p vₛ vᵤ adj_vₛ_vᵤ
    · intro H
      cases H with
      | intro k eq =>
        simp [Walk.length, Even, Odd] at eq
        have wEv : Odd walk_vᵤ_vₜ.length := by
          simp [eq]
          rw [← Nat.odd_iff_not_even]
          have plus_one_even : Even (walk_vᵤ_vₜ.length + 1) := by
            simp [eq]
          rw [Nat.even_add_one] at plus_one_even
          rw [← Nat.odd_iff_not_even] at plus_one_even
          exact plus_one_even
        apply ih.left at wEv
        have s_t_diff_color := adjacent_impl_color_ne G p vₛ vᵤ adj_vₛ_vᵤ
        symm at wEv
        exact fin_2_ne_c_impl_eq (p.color vₛ) (p.color vₜ) (p.color vᵤ) s_t_diff_color wEv

end VertexColoring

end LeanHoG
