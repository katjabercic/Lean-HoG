-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edge : fin vertex_size → fin vertex_size → bool)
  (irreflexive : (∀ i, ¬ edge i i) . bool_reflect)
  (symmetric : (∀ i j, edge i j → edge j i) . bool_reflect)

-- The type of vertices of g
@[simp, reducible]
def vertex (g : simple_irreflexive_graph) := fin (g.vertex_size)

def edge_size (g : simple_irreflexive_graph) : ℕ :=
  fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }

class hog_edge_size (g : simple_irreflexive_graph) : Type :=
  (edge_size_val : ℕ)
  (edge_size_eq : edge_size g = edge_size_val . obviously)

-- add an edge to a graph
def add_edge (g : simple_irreflexive_graph) (x y : vertex g) (ne : x ≠ y) : simple_irreflexive_graph :=
  { vertex_size := g.vertex_size
  , edge := λ i j, (i, j) = (x, y) ∨ (j, i) = (x, y) ∨ g.edge i j
  , irreflexive := begin simp [g.irreflexive]; assumption end
  , symmetric := begin simp_intros i j p, have := g.symmetric i j, tauto end
  }
