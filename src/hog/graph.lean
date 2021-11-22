-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edge : fin vertex_size → fin vertex_size → bool)
  (irreflexive : (∀ i, ¬ edge i i) . bool_reflect)
  (symmetric : (∀ i j, edge i j → edge j i) . bool_reflect)


@[reducible]
def to_simple_graph (g : simple_irreflexive_graph) : simple_graph (fin g.vertex_size) :=
{ simple_graph . 
  adj := λ i j, g.edge i j = tt,
  sym := g.symmetric,
  loopless := g.irreflexive
}

def edge_size (g : simple_irreflexive_graph) : ℕ :=
  fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }

class hog_edge_size (g : simple_irreflexive_graph) : Type :=
  (edge_size_val : ℕ)
  (edge_size_eq : edge_size g = edge_size_val . obviously)

def max_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.max_degree (to_simple_graph g)

class hog_max_degree (g : simple_irreflexive_graph) : Type :=
  (val : ℕ)
  (mag_degree_eq : max_degree g = val . obviously)