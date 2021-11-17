import combinatorics.simple_graph.basic
import tactic
open interactive (parse)
open interactive.types (texpr)
open lean.parser (tk)

-- A tactic which generate a simple graph on n vertices from its adjacency relations.
-- The vertices are assumed to be of type fin n, and the adjacency relation has type ℕ → ℕ → bool.
meta def tactic.interactive.from_adjacency (n : parse texpr) (_ : parse $ tk "with") (adj : parse texpr) : tactic unit :=
do { r ← tactic.i_to_expr_strict
                  ``(simple_graph.mk
                      (λ i j, (%%adj) i.val j.val)
                      (begin unfold symmetric, exact (to_bool_iff _).mp rfl end)
                      (begin unfold irreflexive, exact (to_bool_iff _).mp rfl end) : simple_graph (fin %%n)
                  ),
     tactic.exact r
}
