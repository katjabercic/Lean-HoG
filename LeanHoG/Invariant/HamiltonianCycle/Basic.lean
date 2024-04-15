
import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

@[simp] def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (v : g.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (g : Graph)  where
  u : g.vertex
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

def Graph.isHamiltonian (g : Graph) : Prop :=
  ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian

@[simp] def Graph.isNonHamiltonian (g : Graph) : Prop := ¬ g.isHamiltonian

@[simp] def Graph.isNonHamiltonian' {g : Graph} : Prop :=
  ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

namespace HamiltonianCycle

instance {g : Graph} : Repr (HamiltonianCycle g) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr (HamiltonianCycle g) where
  reprPrec p n := reprPrec p.2.cycle n

@[simp] theorem cycle_of_cert {g : Graph} [hp : HamiltonianCycle g] : g.isHamiltonian := by
  let ⟨u, p, cond⟩ := hp
  apply Exists.intro u
  apply Exists.intro p
  apply cond

instance {G : Graph} [HamiltonianCycle G] : Decidable (G.isHamiltonian) :=
  .isTrue cycle_of_cert

theorem equivNonHamiltonianDefs (g : Graph) :
  g.isNonHamiltonian ↔ g.isNonHamiltonian' :=
  by simp [Graph.isHamiltonian]

end HamiltonianCycle
end LeanHoG
