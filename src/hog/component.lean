-- -- Graph components
import logic.relation
-- import tactic.rcases
-- import data.quot
import .graph

open relation

#eval to_string (@fin.mk 5 3 (nat.lt_of_sub_eq_succ rfl))

@[simp, reducible]
def connected (g : simple_irreflexive_graph) : fin g.vertex_size → fin g.vertex_size → Prop :=
  eqv_gen (λ i j, g.edge i j)

lemma connected_trans {g : simple_irreflexive_graph} {i j k : fin g.vertex_size} (cij : connected g i j) (cjk : connected g j k) : connected g i k :=
begin
  apply eqv_gen.trans,
  assumption,
  assumption
end

lemma connected_symm {g : simple_irreflexive_graph} {i j : fin g.vertex_size} (cij : connected g i j) : connected g j i :=
begin
  apply eqv_gen.symm,
  assumption
end

def add_edge (g : simple_irreflexive_graph) (x : fin g.vertex_size) (y : fin g.vertex_size) : simple_irreflexive_graph :=
{ vertex_size := g.vertex_size,
  edge :=
    (λ (i : fin g.vertex_size) (j : fin g.vertex_size), (¬x = y ∧ ((i = x ∧ j = y) ∨ (i = y ∧ j = x))) ∨ g.edge i j),
  edge_decidable := 
    begin 
      intros i j ,
      simp,
      have d : decidable (g.edge i j ) := g.edge_decidable i j,
      exact @or.decidable (¬x = y ∧ (i = x ∧ j = y ∨ i = y ∧ j = x)) (g.edge i j) (by apply_instance) d
    end,
  irreflexive := 
    begin
      intro i, 
      by_contra,
      cases h,
      {
        cases h,
        cases h_right,
        cc,
        cases h_right,
        cc
      },
      {
        apply g.irreflexive i h
      }
    end,
  symmetric :=
    begin 
      intros i j h,
      cases h,
      tautology,
      apply or.inr,
      apply g.symmetric i j h
    end
}

-- if we add the edge x-y then x and y are connected
lemma connected_added_edge {g : simple_irreflexive_graph} {x y : fin g.vertex_size} :
  connected (add_edge g x y) x y :=
begin
  by_cases x = y,
  { rw h, apply eqv_gen.refl },
  { 
    apply eqv_gen.rel,
    dunfold add_edge,
    simp,
    apply or.inl h
  }
end

-- connected vertices are still connected when we add an edge
lemma connected_after_add_edge {g : simple_irreflexive_graph} {x y : fin g.vertex_size} (i j : fin g.vertex_size) :
  connected g i j → connected (add_edge g x y) i j :=
begin
  intro gij,
  apply @eqv_gen_mono _ i j g.edge,
  { intros i j gij, dunfold add_edge, simp, tautology },
  { assumption }
end

structure decomposition (g : simple_irreflexive_graph) : Type :=
  (anchor : fin g.vertex_size → fin g.vertex_size)
  (anchor_is_kernel : ∀ i j, anchor i = anchor j ↔ connected g i j)

lemma ite_id {α : Type} [decidable_eq α] {x y : α} :
  (if x = y then y else x) = x :=
begin
  by_cases x = y ; simp ; intro; symmetry; assumption  
end

lemma connected_add_edge_options {g : simple_irreflexive_graph} {i j x y : fin g.vertex_size} (cxyij : connected (add_edge g x y) i j) : 
  connected g i j ∨ (connected g i x ∧ connected g j y) ∨ (connected g j x ∧ connected g i y) :=
begin
  by_cases cij : connected g i j,
  apply or.inl cij,
  apply or.inr,
  by_cases h : connected g i x ∧ connected g j y,
  apply or.inl h,
  apply or.inr,
  sorry
end

lemma decomposition_add_edge {g : simple_irreflexive_graph} (D : decomposition g) (x y : fin g.vertex_size) : decomposition (add_edge g x y) :=
{ anchor := (λ i, if D.anchor i = D.anchor x then D.anchor y else D.anchor i), 
  anchor_is_kernel :=
    begin
      intros i j,
      split,
      {
        intro h,
        by_cases aiax : D.anchor i = D.anchor x; by_cases ajax : D.anchor j = D.anchor x,
        {
          have aiaj : D.anchor i = D.anchor j := by cc,
          have cij : connected g i j := begin apply iff.mp, apply D.anchor_is_kernel i j, exact aiaj end,
          apply connected_after_add_edge,
          exact cij
        },
        {
          suffices h' : connected (add_edge g x y) i x ∧ connected (add_edge g x y) x y ∧ connected (add_edge g x y) y j,
            cases h',
            cases h'_right,
            apply connected_trans h'_left,
            apply connected_trans h'_right_left,
            exact h'_right_right,
          split,
            have cix : connected g i x := begin apply iff.mp, apply D.anchor_is_kernel i x, exact aiax end,
            apply connected_after_add_edge, exact cix,
          split,
            apply connected_added_edge,
          have cyj : connected g y j := begin simp [aiax, ajax] at h, apply iff.mp, apply D.anchor_is_kernel y j, exact h end,
          apply connected_after_add_edge, exact cyj
        },
        {
          suffices h' : connected (add_edge g x y) i y ∧ connected (add_edge g x y) x y ∧ connected (add_edge g x y) x j,
            cases h',
            cases h'_right,
            apply connected_trans h'_left,
            apply connected_trans, apply connected_symm h'_right_left,
            exact h'_right_right,
          simp [aiax, ajax] at h,
          split,
            apply connected_after_add_edge,
            apply iff.mp,
            apply D.anchor_is_kernel i y,
            exact h,
          split,
            apply connected_added_edge,
          apply connected_after_add_edge,
          apply connected_symm,
          apply iff.mp,
          apply D.anchor_is_kernel j x,
          exact ajax
        },
        {
          simp [aiax, ajax] at h,
          apply connected_after_add_edge,
          apply iff.mp,
          apply D.anchor_is_kernel i j,
          exact h
        }
      },
      {
        intro h,
        by_cases aiax : D.anchor i = D.anchor x; by_cases ajax : D.anchor j = D.anchor x,
        {
          simp [aiax, ajax]
        },
        {
          simp [aiax, ajax],
          -- suffices cyj : connected (add_edge g x y) y j,
          apply iff.mpr,
          apply D.anchor_is_kernel,
          have cix : connected g i x := begin apply iff.mp, apply D.anchor_is_kernel, exact aiax end,
          have ncjx : ¬ connected g j x := 
            begin 
              by_contra, 
              have h' : D.anchor j = D.anchor x := begin apply iff.mpr, apply D.anchor_is_kernel, exact h end,
              contradiction
            end,
          have ncij : ¬ connected g i j := 
            begin 
              by_contra,  
              have cjx : connected g j x := begin apply connected_trans, apply connected_symm h, exact cix end,
              contradiction
            end,
          have h' := connected_add_edge_options h,
          have h'' : connected g i x ∧ connected g j y ∨ connected g j x ∧ connected g i y := begin apply or.resolve_left h', exact ncij end,
          have h''' : connected g i x ∧ connected g j y :=
            begin
              apply or.resolve_right h'',
              by_contra,
              cases h,
              contradiction
            end,
          cases h''',
          apply connected_symm,
          exact h'''_right
        },
        {
          simp [aiax, ajax],
          sorry
        },
        {
          simp [aiax, ajax],
          sorry
        }
      }
    end
}