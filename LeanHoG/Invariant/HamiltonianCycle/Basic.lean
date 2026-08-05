import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

/-- A Hamiltonian cycle is a cycle which visits each vertex exactly once.

The definition of a `Cycle` already ensures that each vertex is visited at most once,
so this definition just adds that each vertex is indeed visited. -/
def Cycle.isHamiltonian {G : Graph} {u : G.vertex} (c : Cycle G u) : Bool :=
  ∀ (v : G.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (G : Graph)  where
  u : G.vertex
  cycle : Cycle G u
  isHamiltonian : cycle.isHamiltonian = true

/-- A `Graph` is Hamiltonian if it contains a Hamiltonian cycle. -/
def Graph.isHamiltonian (G : Graph) : Prop :=
  ∃ (u : G.vertex) (c : Cycle G u), c.isHamiltonian

@[simp] def Graph.isNonHamiltonian (G : Graph) : Prop := ¬ G.isHamiltonian

@[simp] def Graph.isNonHamiltonian' {G : Graph} : Prop :=
  ∀ (u : G.vertex) (c : Cycle G u), ¬c.isHamiltonian

namespace HamiltonianCycle

instance {G : Graph} : Repr (HamiltonianCycle G) where
  reprPrec p n := reprPrec p.cycle n

@[simp] theorem cycle_of_cert {G : Graph} [hc : HamiltonianCycle G] : G.isHamiltonian := by
  let ⟨u, c, cond⟩ := hc
  apply Exists.intro u
  apply Exists.intro c
  apply cond

instance {G : Graph} [HamiltonianCycle G] : Decidable (G.isHamiltonian) :=
  .isTrue cycle_of_cert

theorem equivNonHamiltonianDefs (G : Graph) :
  G.isNonHamiltonian ↔ G.isNonHamiltonian' :=
  by simp [Graph.isHamiltonian]

end HamiltonianCycle
end LeanHoG
