-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edge : fin vertex_size → fin vertex_size → Prop)
  [edge_decidable : decidable_rel edge]
  (irreflexive : (∀ i, ¬ edge i i) . bool_reflect)
  (symmetric : (∀ i j, edge i j → edge j i) . bool_reflect)

-- The type of vertices of g
@[simp, reducible]
def vertex (g : simple_irreflexive_graph) := fin (g.vertex_size)

def edge_size (g : simple_irreflexive_graph) : ℕ :=
begin
  haveI := g.edge_decidable,
  exact fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }
end

class hog_edge_size (g : simple_irreflexive_graph) : Type :=
  (edge_size_val : ℕ)
  (edge_size_eq : edge_size g = edge_size_val . obviously)

-- add an edge to a graph
@[reducible]
def add_edge (g : simple_irreflexive_graph) (x y : vertex g) : simple_irreflexive_graph :=
begin
  haveI := g.edge_decidable,
  exact
  { vertex_size := g.vertex_size
  , edge := λ i j, (x ≠ y ∧ ((i, j) = (x, y) ∨ (j, i) = (x, y))) ∨ g.edge i j
  , irreflexive := begin simp [g.irreflexive]; assumption end
  , symmetric := begin simp_intros i j p, have := g.symmetric i j, tauto end
  }
end

-- adding a loop does nothing
def add_loop (g : simple_irreflexive_graph) (x y z : vertex g) :
  g.edge x y ↔ (add_edge g z z ).edge x y :=
begin
  simp
end