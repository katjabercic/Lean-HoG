import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.HamiltonianPath.Basic

namespace LeanHoG

def Graph.hypotraceable (G : Graph) : Prop :=
  ¬ G.traceable ∧ ∀ (v : G.vertex), (G.deleteVertex v).traceable

/-! `Graph.hypotraceable` is a conjunction over `G` and all of its one-vertex deletions, so
deciding it means `G.vertexSize + 1` separate calls to `searchForHamiltonianPathAux`. The
three lemmas below are the introduction and elimination steps the elaborator needs; stating
them here keeps the meta code to `Meta.mkAppM` and off `Expr` surgery. -/

theorem hypotraceable_of_deletions {G : Graph} (h : ¬ G.traceable)
    (hv : ∀ (v : G.vertex), (G.deleteVertex v).traceable) : G.hypotraceable := ⟨h, hv⟩

theorem not_hypotraceable_of_traceable {G : Graph} (h : G.traceable) : ¬ G.hypotraceable :=
  fun hyp => hyp.1 h

theorem not_hypotraceable_of_deletion {G : Graph} (v : G.vertex)
    (h : ¬ (G.deleteVertex v).traceable) : ¬ G.hypotraceable := fun hyp => h (hyp.2 v)

/-- A graph with no vertices is hypotraceable: it is not traceable for want of a vertex to
start at, and the condition on deletions is vacuous because there is nothing to delete.

`searchForHypotraceabilityAux` no longer needs this as a special case — it reaches the same
conclusion generically, `searchForHamiltonianPathAux` having become total at this size (see
`no_hamiltonian_path_on_size_0`). It is kept as a statement of the fact in its own right. -/
theorem hypotraceable_on_size_zero {G : Graph} (h : G.vertexSize = 0) : G.hypotraceable := by
  constructor
  · apply no_hamiltonian_path_on_size_0 h
  · intro v
    exact absurd v.isLt (by omega)

end LeanHoG
