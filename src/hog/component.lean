-- -- Graph components
import logic.relation
import .graph
open relation

-- We need the following induction on connectedness
-- If u ≈ v then there is a path of length k connecting them.
-- Then either :
---- u = v, or
---- (u,v) ∈ E(G), or
---- ∃ w ∈ V(G) s.t. (u,w) ∈ E(G) ∧ w ≈ v with a path of length (k-1)

-- So again we find ourselves in the situation where we want to have paths between vertices to express connectedness



@[simp, reducible]
def connected {g : simple_irreflexive_graph} : fin g.vertex_size → fin g.vertex_size → Prop := eqv_gen g.edge

notation v ≈ u := connected v u

@[simp]
lemma edge_connected {g : simple_irreflexive_graph} {v u : fin g.vertex_size} (e : g.edge v u) : v ≈ u := eqv_gen.rel v u e

@[simp]
lemma connected_refl {g : simple_irreflexive_graph} {v : fin g.vertex_size} : v ≈ v := eqv_gen.refl v

@[simp]
lemma connected_trans {g : simple_irreflexive_graph} {v u w : fin g.vertex_size} (cvu : v ≈ u) (cuw : u ≈ w) : v ≈ w := eqv_gen.trans v u w cvu cuw

notation p ⊕ q := connected_trans p q

@[simp]
lemma connected_symm {g : simple_irreflexive_graph} {v u : fin g.vertex_size} (cvu : v ≈ u) : u ≈ v := eqv_gen.symm v u cvu

notation p ↑ := connected_symm p

-- because connectedness if defined as an equivalence relation, two connectedertices can't be equal
@[simp]
lemma not_connected_not_equal {g : simple_irreflexive_graph} {v u : fin g.vertex_size} : ¬v ≈ u → ¬v = u :=
begin
  intro h,
  by_contra,
  suffices h' : v ≈ u,
  contradiction,
  simp [h],
  apply eqv_gen.refl,
end

-- I don't particularly like this formulation because it doesn't give us an edge we can work with, it just pushes things to induction without giving a good induction hypothesis
lemma connected_induction {g : simple_irreflexive_graph} {v u : fin g.vertex_size} : v ≈ u → (v = u) ∨ g.edge v u ∨ ∃ w, v ≈ w ∧ w ≈ u :=
begin
  intro cvu,
  induction cvu with x y h x x y exy h x y z exy eyz h₁ h₂,
  { apply or.inr, apply or.inl h },
  { apply or.inl, refl },
  { cases h,
      apply or.inl,
      symmetry,
      assumption,
    apply or.inr,
    cases h,
      apply or.inl,
      apply g.symmetric,
      assumption,
    apply or.inr,
    cases h with w h,
    apply exists.intro w,
    cases h with cxw cwy,
    exact ⟨ cwy ↑, cxw ↑ ⟩
  },
  { cases h₁,
    cases h₂,
      apply or.inl,
      transitivity,
      exact h₁,
      exact h₂,
    rw h₁,
      apply or.inr,
      assumption,
    cases h₂,
    rw ← h₂,
      apply or.inr,
      assumption,
    apply or.inr,
    cases h₁,
    cases h₂,
      apply or.inr,
      apply exists.intro y,
      split,
      apply edge_connected h₁,
      apply edge_connected h₂,
    apply or.inr,
      cases h₂ with w h,
      apply exists.intro y,
      split,
      apply edge_connected h₁,
      cases h with cyw cwz,
      exact cyw ⊕ cwz,
    cases h₂,
      apply or.inr,
      cases h₁ with w h,
      apply exists.intro w,
      split,
      cases h,
      assumption,
      cases h with cxw cwy,
      have cyz : y ≈ z,
        assumption,
      exact cwy ⊕ cyz,
    cases h₁ with w h₁,
    cases h₂ with t h₂,
    apply or.inr,
    apply exists.intro w,
    cases h₁ with cxw cwy,
    split,
    assumption,
    cases h₂ with cyt ctz,
    exact cwy ⊕ cyt ⊕ ctz
  }
end

lemma better_induction {g : simple_irreflexive_graph} {v u : fin g.vertex_size} : v ≈ u → Prop := sorry


def connected_graph : simple_irreflexive_graph → Prop := λ G, Π (u v : fin G.vertex_size), u ≈ v

structure number_of_connected_components : Type :=
  (G : simple_irreflexive_graph)
  (num_components : ℕ)
  (c : fin G.vertex_size → fin num_components)
  (has_enough : ∀ (i : fin num_components), ∃ u, c(u) = i)
  (conn : ∀ u v, c(u) = c(v) ↔ u ≈ v)

structure num_components_witness : Type :=
  (G : simple_irreflexive_graph)
  (num_components : ℕ)
  (c : fin G.vertex_size → fin num_components)
  (h : fin G.vertex_size → ℕ)
  (has_enough : ∀ i, ∃ u, c u = i)
  (connect_edges : ∀ u v, G.edge u v → c u = c v)
  (root : fin num_components → fin G.vertex_size)
  (is_root :  ∀ i, c (root i) = i ∧ h (root i) = 0)
  (uniqueness_of_roots : ∀ v : fin G.vertex_size, h v = 0 → v = root (c v)) -- can we get rid of this condition?
  (height_cond : ∀ v, 0 < h v → ∃ u, (G.edge u v) ∧ (h u < h v))

lemma connected_to_root (w : num_components_witness) : Π v : fin w.G.vertex_size, v ≈ w.root (w.c v) :=
begin
  intro v,
  sorry
end

def witness_components : num_components_witness → number_of_connected_components :=
λ w,
{
  G := w.G,
  num_components := w.num_components,
  c := w.c,
  has_enough := w.has_enough,
  conn :=
    begin
      intros u v,
      split,
      { intro H,
        have connected_to_root : ∀ x : fin w.G.vertex_size, x ≈ w.root (w.c x),
        { intro x,
          apply connected_to_root
        },
        { have h : u ≈ w.root (w.c u) := connected_to_root u,
          have h' : v ≈ w.root (w.c v) := connected_to_root v,
          have h'' : w.root (w.c u) = w.root (w.c v) := by rw H,
          rw h'' at h,
          exact h ⊕ (h' ↑)
        }
      },
      { intro h,
        induction h,
        { apply w.connect_edges, assumption }, -- The path u ~> v is just an edge
        { refl }, -- reflexivity
        { symmetry, assumption }, -- symmetry
        { transitivity; assumption } --transitivity
      }
    end
}