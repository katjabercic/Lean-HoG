import .graph
import .component


-- [ ] Be able to define the functions on paths my pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive path {g : simple_irreflexive_graph} : fin g.vertex_size → fin g.vertex_size → Type
| trivial (s : fin g.vertex_size) : path s s
| left (s t u : fin g.vertex_size) : g.edge s t → path t u →  path s u
| right (s t u : fin g.vertex_size) : g.edge t u → path s t → path s u

-- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
-- notation p ,, next  := path.right next p
-- notation next ,, p := path.left next p

def symm_path {g : simple_irreflexive_graph} {s t : fin g.vertex_size} :  path s t → path t s :=
begin
  intro p,
  induction p with p s t n e p p',
    constructor,
  { 
    apply path.right,
    apply g.symmetric,
    exact e,
    exact p'
  },
  {
    apply path.left,
    apply g.symmetric,
    exact p_ᾰ,
    exact p_ih
  }
end

def concat_path {g : simple_irreflexive_graph} {s t u : fin g.vertex_size} : path s t → path t u → path s u :=
begin
  intros p q,
  induction p with s' t' n u' e p',
    exact q,
  {
    apply path.left,
    exact e,
    apply p_ih,
    exact q
  },
  {
    apply p_ih,
    apply path.left,
    exact p_ᾰ,
    exact q
  }
end

notation p + q := concat_path p q

def edge_path {g : simple_irreflexive_graph} {s t : fin g.vertex_size} : g.edge s t → path s t :=
begin
  intro est,
  apply path.left s t t est (path.trivial t)
end

def length {g : simple_irreflexive_graph} {s t : fin g.vertex_size} : path s t → ℕ :=
begin
  intro p,
  induction p with p s t n e p l _ _ _ _ _ l,
  exact 0,
  exact l + 1,
  exact l + 1
end

def vertices {g : simple_irreflexive_graph} {s t : fin g.vertex_size} : path s t → set (fin g.vertex_size) :=
begin
  intro p,
  induction p,
  exact {p},
  apply set.insert p_s p_ih,
  apply set.insert p_t p_ih
end

def inner_vertices {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : path s t → set (fin g.vertex_size) :=
λ p, set.inter (vertices p) {s, t}

def edges {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : path s t → set (edge g) :=
begin
  intro p,
  induction p,
  exact ∅,
  let u : edge g := { i := p_s, j := p_t, H := p_ᾰ },
  apply set.insert u p_ih,
  let v : edge g := { i := p_t, j := p_u, H := p_ᾰ },
  apply set.insert v p_ih
end

-- With the current definition of the function to compute edges and vertices, these two functions are noncomputable if they map into bool
-- Here we probably want to use BST's again to make everything computable and decidable
def vertex_independent {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : path s t → path s t → Prop :=
λ p q, (inner_vertices s t p) ∩ (inner_vertices s t q) = ∅

def edge_independent {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : path s t → path s t → Prop :=
λ p q, (edges s t p) ∩ (edges s t q) = ∅


-- The easy direction, just apply induction on the structure of path
lemma path_implies_connected {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : path s t → s ≈ t :=
begin
  intro h,
  induction hn : h with s s t u est p ih s t u etu p ih,
  { apply connected_refl },
  { have ctu : t ≈ u, apply ih p, refl,
    have cst : s ≈ t, apply edge_connected est,
    exact cst ⊕ ctu
  },
  { have cst : s ≈ t, apply ih p, refl,
    have ctu : t ≈ u, apply edge_connected etu,
    exact cst ⊕ ctu
  }
end

#check eqv_gen.drec_on

-- The harder direction, we need to find a path for connected vertices
-- Again we're going to use induction on the structure of the connected relation and try to construct a path inductively
-- The problem is that eqv_gen only has a recursor into Prop
-- !!! USES CLASSICAL REASONING !!!
lemma connected_implies_path {g : simple_irreflexive_graph} (s t : fin g.vertex_size) : s ≈ t → ∃ p : path s t, p = p :=
begin
  intro h,
  induction hn : h with x y exy x x y exy ih x y z exy eyz ih ih',
  { apply exists.intro,
    refl,
    apply path.left x y y exy,
    apply path.trivial
  },
  { apply exists.intro,
    refl,
    apply path.trivial
  },
  { apply exists.intro,
    refl,
    have H : (∃ (p : path x y), p = p),
    apply ih,
    refl,
    have p : path x y,
    apply exists.classical_rec_on H, -- !!!! CLASSICAL REASONING !!!! --
    intro q,
    intro _,
    exact q,
    apply symm_path p,
  },
  { apply exists.intro,
    refl,
    have H : (∃ (p : path x y), p = p),
    apply ih,
    refl,
    have p : path x y,
    apply exists.classical_rec_on H, -- !!!! CLASSICAL REASONING !!!! --
    intro q,
    intro _,
    exact q,
    have H' : (∃ (p : path y z), p = p),
    apply ih',
    refl,
    have q : path y z,
    apply exists.classical_rec_on H',  -- !!!! CLASSICAL REASONING !!!! --
    intro q,
    intro _,
    exact q,
    exact p + q
  }
end

lemma ind_conn_path (w : num_components_witness) (v: fin w.G.vertex_size) : 
  (∀ u, (w.h u < w.h v ∧ w.G.edge v u → path u (w.root (w.c u)))) → path v (w.root (w.c v)) :=
begin
  intro h,
  by_cases H : (0 < w.h v),
  { let u := w.next v,
    have hyp := w.height_cond v H,
    have p : path u (w.root (w.c u)) :=
      begin 
        apply h,
        split,
        cases hyp,
        exact hyp_right,
        cases hyp,
        apply w.G.symmetric,
        exact hyp_left
      end,
    have same_c : w.c u = w.c v := begin apply w.connect_edges, cases hyp, assumption end,
    rw ← same_c,
    have q : path v u := begin apply edge_path, cases hyp, apply w.G.symmetric, exact hyp_left end,
    exact q + p
  },
  {
    simp at H,
    have h := w.uniqueness_of_roots v H,
    rw ← h,
    apply path.trivial
  }
end

lemma witness_path_to_root (w : num_components_witness) (s : fin w.G.vertex_size) : ∃ p : path s (w.root (w.c s)), p = p :=
begin
  apply @bar (fin w.G.vertex_size) (w.h) (λ v, ∃ p : path v (w.root (w.c v)), p = p),
  intro v,
  by_cases H : (0 < w.h v),
  { let u := w.next v,
    have hyp := w.height_cond v H,
    intro h,
    have H' : ∃ p : path u (w.root (w.c u)), p = p :=
      begin
        apply h,
        cases hyp,
        exact hyp_right
      end,
    have same_c : w.c u = w.c v := begin apply w.connect_edges, cases hyp, assumption end,
    rw ← same_c,
    have q : path v u := begin apply edge_path, cases hyp, apply w.G.symmetric, exact hyp_left end,
    sorry
  },
  {
    simp at H,
    have h := w.uniqueness_of_roots v H,
    rw ← h,
    apply path.trivial
  }
end


def recursive_path (w : num_components_witness) : Π v : fin w.G.vertex_size, path v (w.root (w.c v)) :=
begin
  intro v,
  by_cases H : (0 < w.h v),
  { 
    let u := w.next v,
    have p := recursive_path u,
  },
  {
    simp at H,
    have h := w.uniqueness_of_roots v H,
    rw ← h,
    apply path.trivial
  }
end 

lemma witness_to_path (w : num_components_witness) (s t : fin g.vertex_size) : s ≈ t → path s t :=
begin
  intro cst,
  sorry
end