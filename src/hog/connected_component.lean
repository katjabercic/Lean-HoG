-- -- Graph components
import logic.relation
import .graph
import .tree_representation
import .tree_set
open relation


@[simp, reducible]
def connected (G : simple_irreflexive_graph) : ℕ → ℕ → Prop := eqv_gen (edge_relation G)

-- notation g | v ≈ u := connected g v u

@[simp]
lemma edge_connected {G : simple_irreflexive_graph} {u v : ℕ} (e : (edge_relation G) u v) : 
  connected G u v := eqv_gen.rel u v e

@[simp]
lemma connected_refl {G : simple_irreflexive_graph} {v : ℕ} : connected G v v := eqv_gen.refl v

@[simp]
lemma connected_trans {G : simple_irreflexive_graph} {u v w : ℕ} (cuv : connected G u v) (cvw : connected G v w) : 
  connected G u w := eqv_gen.trans u v w cuv cvw

notation p ⊕ q := connected_trans p q

@[simp]
lemma connected_symm {G : simple_irreflexive_graph} {u v : ℕ} (cuv : connected G u v) : 
  connected G v u := eqv_gen.symm u v cuv

notation p ↑ := connected_symm p

-- because connectedness if defined as an equivalence relation, two connectedertices can't be equal
@[simp]
lemma not_connected_not_equal {G : simple_irreflexive_graph} {u v : ℕ} : ¬connected G u v → ¬u = v :=
begin
  intro h,
  by_contra,
  suffices h' : connected G u v,
  contradiction,
  simp [h],
  apply eqv_gen.refl,
end

def connected_graph : simple_irreflexive_graph → Prop := λ G, Π (u v : ℕ), connected G u v

structure number_of_connected_components : Type :=
  (G : simple_irreflexive_graph)
  (num_components : ℕ)
  (c : ℕ → fin num_components) -- assigns components to vertices
  (has_enough : ∀ (i : fin num_components), ∃ u, c(u) = i)
  (conn : ∀ u v, c(u) = c(v) ↔ connected G u v)

structure num_components_witness : Type :=
  (G : simple_irreflexive_graph)
  (num_components : ℕ)
  (c : ℕ → fin num_components)
  (h : ℕ → ℕ)
  (connect_edges : ∀ (e : Edge), e ∈ G.edges → c (e.edge.fst) = c (e.edge.snd))
  (root : fin num_components → ℕ)
  (is_root :  ∀ i, c (root i) = i ∧ h (root i) = 0)
  (uniqueness_of_roots : ∀ v, h v = 0 → v = root (c v)) -- can we get rid of this condition?
  (next : ℕ → ℕ) -- for each vertex with height > 0, give a neighbor with lower height
  (height_cond : ∀ v, (0 < h v) → (edge_relation G) (next v) v ∧ h (next v) < h v)

theorem foo (α : Type) (f : α → ℕ) (P : α → Prop)
  (base : ∀ a, f a = 0 → P a)
  (ind : ∀ a, (∀ b, f b < f a → P b) → P a) :
  ∀ a, P a :=
begin
  intro a,
  let Q := λ n, ∀ a, f a = n → P a,
  have Qstep : ∀ (n : ℕ), (∀ (m : ℕ), m < n → Q m) → Q n,
  { intros n h a ξ,
    apply (ind a),
    intros b fb_lt_fa,
    rewrite ξ at fb_lt_fa,
    apply (h (f b)) fb_lt_fa, refl 
  },
  exact @well_founded.fix _ Q nat.lt nat.lt_wf Qstep (f a) a rfl,
end

theorem bar (α : Type) (f : α → ℕ) (P : α → Prop)
  (ind : ∀ a, (∀ b, f b < f a → P b) → P a) :
  ∀ a, P a :=
begin
  intro a,
  induction hn : f a using nat.strong_induction_on with n ih generalizing a,
  apply ind,
  intros b fb_lt_fa,
  rw hn at fb_lt_fa,
  exact ih _ fb_lt_fa _ rfl,
end

lemma connected_to_root (w : num_components_witness) : 
  ∀ v : ℕ, connected w.G v (w.root (w.c v)) :=
begin
  fapply @foo ℕ (w.h) (λ u, connected w.G u (w.root (w.c u))),
  { intros v h,
    have h := w.uniqueness_of_roots v h,
    rw ← h,
    apply connected_refl
  },
  { intros v h,
    by_cases H : (0 < w.h v),
    { let u := w.next v,
      have hyp := w.height_cond v H,
      have H' : connected w.G u (w.root (w.c u)) := begin apply h, cases hyp, assumption end,
      have same_c : w.c u = w.c v := 
        begin
          apply decidable.lt_by_cases u v,
          { intros uv, -- u < v
            let e := { Edge . edge := (u, v), src_lt_trg := uv },
            have euv : e ∈ w.G.edges,
            cases hyp,
            apply edge_relation_is_mem u v uv hyp_left,
            apply w.connect_edges e euv,
          },
          { intros uv, -- u = v
            rw uv,
          },
          { intros vu,
            let e := { Edge . edge := (v, u), src_lt_trg := vu },
            have evu : e ∈ w.G.edges,
            cases hyp,
            apply edge_relation_is_mem v u vu (edge_relation_symmetric u v hyp_left),
            symmetry,
            apply w.connect_edges e evu,
          }
        end,
      rw ← same_c,
      have cuv : connected w.G u v := 
        begin apply edge_connected, cases hyp, assumption end,
      exact cuv↑ ⊕ H',
    },
    { simp at H,
      have h := w.uniqueness_of_roots v H,
      rw ← h,
      apply connected_refl
    }
  }
end

lemma witness_connected_condition (w : num_components_witness) : ∀ u v, w.c u = w.c v ↔ connected w.G u v :=
begin
  intros u v,
  split,
  { intro H,
    have connected_to_root : ∀ x : ℕ, connected w.G x (w.root (w.c x)),
    { intro x,
      apply connected_to_root
    },
    { have h : connected w.G u (w.root (w.c u)) := connected_to_root u,
      have h' : connected w.G v (w.root (w.c v)) := connected_to_root v,
      have h'' : w.root (w.c u) = w.root (w.c v) := by rw H,
      rw h'' at h,
      exact h ⊕ (h' ↑)
    }
  },
  { intro h,
    induction h with u v rel_uv,
    { apply decidable.lt_by_cases u v,
      { intro uv,
        let e := { Edge . edge := (u, v), src_lt_trg := uv },
        have euv : e ∈ w.G.edges,
        apply edge_relation_is_mem u v uv rel_uv,
        apply w.connect_edges e euv,
      },
      { intro uv,
        rw uv,
      },
      { intros vu,
        let e := { Edge . edge := (v, u), src_lt_trg := vu },
        have evu : e ∈ w.G.edges,
        apply edge_relation_is_mem v u vu (edge_relation_symmetric u v rel_uv),
        symmetry,
        apply w.connect_edges e evu,
      }
    },
    { refl }, -- reflexivity
    { symmetry, assumption }, -- symmetry
    { transitivity; assumption } --transitivity
  }
end

theorem witness_components : num_components_witness → number_of_connected_components :=
λ w,
{
  G := w.G,
  num_components := w.num_components,
  c := w.c,
  has_enough := -- Proof is too long, we can make this a lot shorter
    begin
      have h : function.has_right_inverse w.c,
      unfold function.has_right_inverse,
      fsplit,
      exact w.root,
      unfold function.right_inverse,
      unfold function.left_inverse,
      intro v,
      have := w.is_root v,
      cases this,
      assumption,
      apply iff.mpr function.surjective_iff_has_right_inverse,
      assumption,
    end,
  conn := by apply witness_connected_condition,
}

