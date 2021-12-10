-- Graph components
import logic.relation
import tactic.rcases
import data.quot
import .graph

open relation


@[simp, reducible]
def connected (g : simple_irreflexive_graph) : vertex g → vertex g → Prop :=
  eqv_gen (λ i j, g.edge i j)

-- if we add the edge x-y then x and y are connected
lemma connected_added_edge {g} {x y : vertex g} :
  connected (add_edge g x y) x y :=
begin
  by_cases x = y,
  { rw h, apply eqv_gen.refl },
  { apply eqv_gen.rel,
    dunfold add_edge, 
    simp, tautology  
  } 
end

-- connected vertices are still connected when we add an edge
lemma connected_after_add_edge {g} {x y : vertex g} (i j : vertex g) :
  connected g i j → connected (add_edge g x y) i j :=
begin
  intro gij,
  apply @eqv_gen_mono _ i j g.edge,
  { intros i j gij, dunfold add_edge, simp, tautology },
  { assumption }
end

structure decomposition (g : simple_irreflexive_graph) : Type :=
  (anchor : vertex g → vertex g)
  (anchor_is_kernel : ∀ i j, anchor i = anchor j ↔ connected g i j )

lemma ite_id {α : Type} [decidable_eq α] {x y : α} :
  (if x = y then y else x) = x :=
begin
  by_cases x = y ; simp ; intro; symmetry; assumption  
end

lemma decomposition_add_edge {g} (D : decomposition g) (x y : vertex g) : decomposition (add_edge g x y) :=
  { anchor := (λ i, if D.anchor i = D.anchor x then D.anchor y else D.anchor i)
  , anchor_is_kernel :=
begin
  intros i j,
  by_cases xEy : x = y,
  { rw xEy, repeat { rw ite_id },
    split,
    { intro aiaj,
      apply connected_after_add_edge, apply (D.anchor_is_kernel i j).mp, assumption
    },
    { intro cij, apply (D.anchor_is_kernel i j).mpr,
      apply @eqv_gen_mono _ i j (add_edge g y y).edge,
      { intros a b, apply (add_loop g a b y).mpr },
      { assumption }
    }
  },
  { by_cases aiax: D.anchor i = D.anchor x; by_cases ajax : D.anchor j = D.anchor x ; simp [aiax, ajax],
    { 
      apply @eqv_gen_mono _ i j g.edge, tautology,
      { apply eqv_gen.trans,
        apply (D.anchor_is_kernel i x).mp aiax,
        apply eqv_gen.symm,
        apply (D.anchor_is_kernel j x).mp ajax }  
    },
    { split,
      { intro ayaj,
        apply eqv_gen.trans i x j,
        { apply @eqv_gen_mono _ i x g.edge, tautology,
          apply (D.anchor_is_kernel i x).mp aiax
        },
        apply eqv_gen.trans x y j,
        { apply eqv_gen.rel, tautology },
        { apply @eqv_gen_mono _ y j g.edge, tautology,
          apply (D.anchor_is_kernel y j).mp ayaj }
      },
      { intro ij,
        apply (D.anchor_is_kernel y j).mpr,
        induction ij with u v H qux la le li a1 a2 p q, 
        { cases H,
          { rcases H with ⟨ xy, (⟨ux, vy⟩ | ⟨vx, uy⟩) ⟩,
            { rw vy, apply eqv_gen.refl },
            { apply (D.anchor_is_kernel y v).mp, cc }
          },
          { have auav := (D.anchor_is_kernel u v).mpr (eqv_gen.rel _ _ H), rw auav at aiax, contradiction }
        },
        { contradiction },
        { sorry },
        { sorry }
      }
    },
    { sorry },
    { sorry}
  }
end