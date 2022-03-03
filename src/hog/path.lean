import .graph
import .component

variable g : simple_irreflexive_graph

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive path : fin g.vertex_size → fin g.vertex_size → Type
| trivial (s : fin g.vertex_size) : path s s
| left (s t u : fin g.vertex_size) : g.edge s t → path t u →  path s u
| right (s t u : fin g.vertex_size) : g.edge t u → path s t → path s u

-- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
notation p ,, next  := path.right next p
notation next ,, p := path.left next p

def symm_path (s t : fin g.vertex_size) :  path g s t → path g t s :=
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

def concat_path (s t u : fin g.vertex_size) : path g s t → path g t u → path g s u :=
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

def vertices (s t : fin g.vertex_size) : path g s t → set (fin g.vertex_size) :=
begin
  intro p,
  induction p,
  exact {p},
  apply set.insert p_s p_ih,
  apply set.insert p_t p_ih
end


def inner_vertices (s t : fin g.vertex_size) : path g s t → set (fin g.vertex_size) :=
λ p, set.inter (vertices g s t p) {s, t}

def edges (s t : fin g.vertex_size) : path g s t → set (edge g) :=
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
def vertex_independent (s t : fin g.vertex_size) : path g s t → path g s t → Prop :=
λ p q, (inner_vertices g s t p) ∩ (inner_vertices g s t q) = ∅

def edge_independent (s t : fin g.vertex_size) : path g s t → path g s t → Prop :=
λ p q, (edges g s t p) ∩ (edges g s t q) = ∅ 