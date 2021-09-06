import data.finset.lattice
import combinatorics.simple_graph.basic

namespace graph_invariant

section

  variables {V : Type} [fintype V] (g : simple_graph V) [decidable_rel g.adj]

  def nbh (x : V) := {y : V // g.adj x y}

  instance nbh_fintype (x : V) : fintype (nbh g x) := subtype.fintype (g.adj x)

  def degree (x : V) : ℕ := fintype.card (nbh g x)

  def max_degree : ℕ := finset.sup (fintype.elems _) (degree g)

end

end graph_invariant
