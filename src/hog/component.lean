-- -- Graph components
import logic.relation
-- import tactic.rcases
-- import data.quot
import .graph

open relation

#eval to_string (@fin.mk 5 3 (nat.lt_of_sub_eq_succ rfl))

@[simp, reducible]
def connected (g : simple_irreflexive_graph) : fin g.vertex_size → fin g.vertex_size → Prop := eqv_gen g.edge

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

-- because connectedness if defined as an equivalence relation, two connected vertices can't be equal
lemma not_connected_not_equal {g : simple_irreflexive_graph} {i j : fin g.vertex_size} : ¬connected g i j → ¬i = j :=
begin
  intro h,
  by_contra,
  suffices h': connected g i j,
  contradiction,
  simp [h],
  apply eqv_gen.refl,
end

@[reducible]
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

def remove_edge (g : simple_irreflexive_graph) (x y : fin g.vertex_size): simple_irreflexive_graph :=
{ vertex_size := g.vertex_size,
  edge :=
    (λ (i : fin g.vertex_size) (j : fin g.vertex_size), if (i = x ∧ j = y) ∨ (i = y ∧ j = x) then false else g.edge i j), 
  edge_decidable := 
    begin 
      intros i j, 
      simp,
      have d : decidable (g.edge i j) := g.edge_decidable i j,
      exact @and.decidable (¬(i = x ∧ j = y ∨ i = y ∧ j = x)) (g.edge i j) (by apply_instance) d
    end,
  irreflexive := 
    begin 
      intro i,
      simp,
      intro h,
      apply g.irreflexive 
    end,
  symmetric := 
    begin 
      intros i j h,
      simp,
      simp at h,
      cases h,
      split,
      tautology,
      apply g.symmetric,
      assumption
    end
}

-- def remove_edges : Π (g : simple_irreflexive_graph), list ((fin g.vertex_size) × (fin g.vertex_size)) → simple_irreflexive_graph
-- | g [] := g
-- | g (e :: es) := remove_edges (remove_edge g e.fst e.snd) es

def comb_list (m : nat) : list nat → list nat
| [] := []
| (n :: ns) := if n < m then n :: comb_list ns else comb_list ns

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

-- if two vertices are not connected, there is no edge between them
lemma not_connected_not_edge {g : simple_irreflexive_graph} {i j : fin g.vertex_size} :
  ¬connected g i j → ¬ g.edge i j :=
begin
  intro h,
  by_contra h',
  simp at h,
  have h'' : eqv_gen g.edge i j := begin apply eqv_gen.rel, exact h' end,
  contradiction
end

-- If two vertices i and j are connected and there is no edge between them, there has to be a vertex k, they are both connected to
-- TODO: Nicer proof
lemma connected_through_vertex {g : simple_irreflexive_graph} {i j : fin g.vertex_size} :
  connected g i j → g.edge i j ∨ ∃k, connected g i k ∧ connected g k j :=
begin
  intro cij,
  by_cases g.edge i j,
    apply or.inl h,
  apply or.inr,
  by_contra h',
  have h'' : (¬∃ (k : fin g.vertex_size), connected g i k ∧ connected g k j) ↔ ∀k, ¬(connected g i k ∧ connected g k j) := by apply not_exists,
  have f : ∀k, ¬(connected g i k ∧ connected g k j) := by apply iff.mp h'' h',
  have f' : ¬(connected g i i ∧ connected g i j) := f i,
  have f'' : connected g i i := by apply eqv_gen.refl,
  simp at f'',
  simp [f''] at f',
  simp at cij,
  contradiction
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

-- adding an edge (x,y) didn't magically add an edge (i,j)
lemma no_edge_after_add_edge {g : simple_irreflexive_graph} {x y : fin g.vertex_size} (i j : fin g.vertex_size) :
  ¬ i = x → ¬ i = y → ¬ j = x → ¬ j = y → ¬ g.edge i j → ¬(add_edge g x y).edge i j :=
begin
  intros nix niy njx njy neij,
  simp [neij],
  intro nxy,
  by_contra,
  cases h,
    cases h,
    contradiction,
  cases h,
  contradiction
end

-- if i is connected to x and we add edge (x,y) then i is connected to y
lemma add_edge_connects_components {g : simple_irreflexive_graph} (x y : fin g.vertex_size) (i : fin g.vertex_size) :
  connected g i x → connected (add_edge g x y) i y
| cix := connected_trans (connected_after_add_edge i x cix) connected_added_edge


-- adding an edge (x,y) only connects vertices that were connected to x and y ano no other
lemma dont_add_extra_paths {g : simple_irreflexive_graph} (x y : fin g.vertex_size) (i j: fin g.vertex_size) :
  ¬connected g i j → ¬connected g i x → ¬connected g i y → ¬connected g j x → ¬connected g j y → ¬connected (add_edge g x y) i j :=
begin
  intros ncij ncix nciy ncjx ncjy,
  by_contra,
  by_cases h' : x = y,
    simp [h'] at h,
    simp at ncij,
    contradiction,
  -- simp at ncij,
  have h'' : ¬g.edge i j := not_connected_not_edge _,
  have f : (add_edge g x y).edge i j ∨ ∃k, connected (add_edge g x y) i k ∧ connected (add_edge g x y) k j := begin apply connected_through_vertex, exact h end,
  have f' : ¬(add_edge g x y).edge i j :=
    begin
      apply no_edge_after_add_edge,
      apply not_connected_not_equal, exact ncix,
      apply not_connected_not_equal, exact nciy,
      apply not_connected_not_equal, exact ncjx,
      apply not_connected_not_equal, exact ncjy,
      exact h''
    end,
  have f'' : ∃ (k : fin (add_edge g x y).vertex_size), connected (add_edge g x y) i k ∧ connected (add_edge g x y) k j :=
    begin
      apply or.resolve_left f,
      exact f'
    end,
  apply exists.elim f'',
  intros k k_conns,
  cases k_conns,
  by_cases eq1 : k = x,
    have ckx : connected g k x := begin simp [eq1], apply eqv_gen.refl end,
  rw (symm eq1) at ncix,
  rw (symm eq1) at ncjx,
  sorry
    -- simp [h',  h'', ncij] at h,
end 

structure decomposition (g : simple_irreflexive_graph) : Type :=
  (anchor : fin g.vertex_size → fin g.vertex_size)
  (anchor_is_kernel : ∀ i j, anchor i = anchor j ↔ connected g i j)

lemma ite_id {α : Type} [decidable_eq α] {x y : α} :
  (if x = y then y else x) = x :=
begin
  by_cases x = y ; simp ; intro; symmetry; assumption  
end

example {g : simple_irreflexive_graph} {i j x y : fin g.vertex_size} (cxyij : connected (add_edge g x y) i j) : 
  (¬connected g i j) → (¬connected g i y ∨ ¬connected g j x) → (connected g i x ∧ connected g j y) := 
begin
  intros hij h,
  cases h,
  sorry
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

