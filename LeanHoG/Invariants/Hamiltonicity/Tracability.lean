import LeanHoG.Walk
import LeanHoG.Invariants.Hamiltonicity.Definition

namespace LeanHoG

def Graph.isTreacable (G : Graph) : Prop :=
  ∃ (u : G.vertex) (c : Cycle G u), c.isHamiltonian

lemma hamiltonian_is_traceable {G : Graph} :
  G.isHamiltonian → G.isTreacable := by
  intro h
  let ⟨u, c, hyp⟩ := h
  sorry

end LeanHoG
