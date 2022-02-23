-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic
import .tree

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edge : fin vertex_size → fin vertex_size → Prop)
  [edge_decidable : decidable_rel edge]
  (irreflexive : (∀ i, ¬ edge i i))
  (symmetric : (∀ i j, edge i j → edge j i))
  (edge_size : ℕ)


def from_edge_list (n : ℕ) (edges : list (ℕ × ℕ)) : simple_irreflexive_graph :=
{ vertex_size := n,
  edge :=
    (λ (i : fin n) (j : fin n), ¬ i = j ∧ (list.mem (i.val, j.val) edges ∨ list.mem (j.val, i.val) edges)),
  edge_decidable := begin intros i j, apply_instance end,
  irreflexive := begin intro i, tautology end,
  symmetric := begin intros i j, tautology end,
  edge_size := edges.length
}

def from_BST (n : ℕ) (tree : BST (lex ℕ ℕ)) : simple_irreflexive_graph :=
{ vertex_size := n,
  edge :=
    (λ (i : fin n) (j : fin n), ¬ i = j ∧ ((BT.edge tree.tree i.val j.val) ∨ (BT.edge tree.tree j.val i.val))),
  edge_decidable := begin intros i j, apply_instance end,
  irreflexive := begin intro i, tautology end,
  symmetric := begin intros i j h, tautology end,
  edge_size := tree.edge_size
}

@[reducible]
def to_simple_graph (g : simple_irreflexive_graph) : simple_graph (fin g.vertex_size) :=
{ simple_graph . 
  adj := λ i j, g.edge i j = tt,
  sym := begin intros i j, simp, apply g.symmetric end,
  loopless := begin intro i, simp, apply g.irreflexive end
}

def edge_size (g : simple_irreflexive_graph) : ℕ :=
begin
  haveI := g.edge_decidable,
  exact fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }
end

class hog_edge_size (g : simple_irreflexive_graph) : Type :=
  (edge_size_val : ℕ)
  (edge_size_eq : edge_size g = edge_size_val . obviously)

noncomputable def max_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.max_degree (to_simple_graph g)

class hog_max_degree (g : simple_irreflexive_graph) : Type :=
  (val : ℕ)
  (mag_degree_eq : max_degree g = val . obviously)

noncomputable def min_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.min_degree (to_simple_graph g)

class hog_min_degree (g : simple_irreflexive_graph) : Type :=
  (val : ℕ)
  (min_degree_eq : min_degree g = val . obviously)

class hog_regular (g : simple_irreflexive_graph) [max : hog_max_degree g] [min : hog_min_degree g] : Type :=
  (hog_regular : max.val = min.val . obviously)

structure edge (g : simple_irreflexive_graph) : Type :=
  (i j : fin g.vertex_size)
  (H : g.edge i j)