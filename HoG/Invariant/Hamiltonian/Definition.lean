import HoG.Graph
import HoG.Walk

namespace HoG

def Path.isHamiltonian {g : Graph} {u v : g.vertex} (p : Path g u v) : Bool :=
  ∀ (w : g.vertex), List.contains p.walk.vertices w

def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (w : g.vertex), List.contains c.cycle.vertices w

class HamiltonianGraph (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  is_hamiltonian : cycle.isHamiltonian = true

def Graph.isNonHamiltonian {g : Graph} : Prop := ¬ ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian
def Graph.isNonHamiltonian' {g : Graph} : Prop := ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

end HoG
