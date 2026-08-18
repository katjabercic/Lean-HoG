import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.HamiltonianCycle.Basic

namespace LeanHoG

def Graph.hypohamiltonian (G : Graph) : Prop :=
  ¬ G.isHamiltonian ∧ ∀ (v : G.vertex), (G.deleteVertex v).isHamiltonian

/-! `Graph.hypohamiltonian` is a conjunction over `G` and all of its one-vertex deletions, so
deciding it means `G.vertexSize + 1` separate calls to `searchForHamiltonianCycleAux`. The three
lemmas below are the introduction and elimination steps the elaborator needs, keeping the meta
code to `Meta.mkAppM`. -/

theorem hypohamiltonian_of_deletions {G : Graph} (h : ¬ G.isHamiltonian)
    (hv : ∀ (v : G.vertex), (G.deleteVertex v).isHamiltonian) : G.hypohamiltonian := ⟨h, hv⟩

theorem not_hypohamiltonian_of_hamiltonian {G : Graph} (h : G.isHamiltonian) :
    ¬ G.hypohamiltonian := fun hyp => hyp.1 h

theorem not_hypohamiltonian_of_deletion {G : Graph} (v : G.vertex)
    (h : ¬ (G.deleteVertex v).isHamiltonian) : ¬ G.hypohamiltonian := fun hyp => h (hyp.2 v)


end LeanHoG
