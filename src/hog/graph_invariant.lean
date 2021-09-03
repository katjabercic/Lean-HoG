import combinatorics.simple_graph.basic

namespace graph_invariant

section fintype_helpers

  def argmax {α : Type} [fintype α] (f : α → ℕ)
    : { x : α | ∀ y , f y ≤ f x } :=
    sorry

end fintype_helpers

section degree

variables {V : Type} [fintype V] (g : simple_graph V) [decidable_rel g.adj]

def nbh (x : V) := {y : V | g.adj x y}

instance nbh_fintype (x : V) : fintype (nbh g x) :=
  begin
    sorry
  end

def degree (x : V) : ℕ := fintype.card (nbh g x)

def max_degree : ℕ := degree g (argmax (degree g))

end degree

end graph_invariant
