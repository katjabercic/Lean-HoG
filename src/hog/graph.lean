-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic
import .tree_representation

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edges : BST Edge)
  (neighborhoods : list (ℕ × list ℕ))

def from_BST (n : ℕ) (tree : BST Edge) : simple_irreflexive_graph :=
{ vertex_size := n,
  edges := tree,
  neighborhoods := BST.neighborhoods tree n
}

def edge (g : simple_irreflexive_graph) (i j : ℕ) : bool :=
begin
  apply (@nat.lt_by_cases i j),
  { intro h, exact (BT.contains g.edges.tree {edge := (i, j)}) },
  { intro _, exact ff},
  { intro h, exact (BT.contains g.edges.tree {edge := (j, i)})}
end

def range_forall (p : ℕ → bool) : ℕ → bool
| 0 := tt
| (nat.succ n) := p n && range_forall n

lemma range_forall_is_forall (p : ℕ → bool) (n : ℕ) :
  range_forall p n = tt → ∀ (k : fin n), p k :=
begin
  induction n,
  { obviously },
  { intro h, sorry }
end

def all_vertices (g : simple_irreflexive_graph) (p : ℕ → bool) :=
  range_forall p g.vertex_size

def all_edges (g : simple_irreflexive_graph) (p : ℕ → ℕ → bool) :=
  BT.forall (λ e, p (Edge.edge e).fst (Edge.edge e).snd) g.edges.tree


-- @[reducible]
-- def to_simple_graph (g : simple_irreflexive_graph) : simple_graph (fin g.vertex_size) :=
-- { simple_graph .
--   adj := λ i j, g.edge i j = tt,
--   sym := begin intros i j, simp, apply g.symmetric end,
--   loopless := begin intro i, simp, apply g.irreflexive end
-- }

-- def edge_size (g : simple_irreflexive_graph) : ℕ :=
-- begin
--   haveI := g.edge_decidable,
--   exact fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }
-- end

-- class hog_edge_size (g : simple_irreflexive_graph) : Type :=
--   (edge_size_val : ℕ)
--   (edge_size_eq : edge_size g = edge_size_val . obviously)

-- noncomputable def max_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.max_degree (to_simple_graph g)

-- class hog_max_degree (g : simple_irreflexive_graph) : Type :=
--   (val : ℕ)
--   (mag_degree_eq : max_degree g = val . obviously)

-- noncomputable def min_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.min_degree (to_simple_graph g)

-- class hog_min_degree (g : simple_irreflexive_graph) : Type :=
--   (val : ℕ)
--   (min_degree_eq : min_degree g = val . obviously)

-- class hog_regular (g : simple_irreflexive_graph) [max : hog_max_degree g] [min : hog_min_degree g] : Type :=
--   (hog_regular : max.val = min.val . obviously)

-- structure edge (g : simple_irreflexive_graph) : Type :=
--   (i j : fin g.vertex_size)
--   (H : g.edge i j)
