import HoG.Graph
import HoG.Walk

namespace HoG

def Path.isHamiltonian {g : Graph} {u v : g.vertex} (p : Path g u v) : Bool :=
  ∀ (w : g.vertex), List.contains p.walk.vertices w

class HamiltonianPath (g : Graph) (u v : g.vertex) where
  path : Path g u v
  isHamiltonian : path.isHamiltonian = true

instance {g : Graph} {u v : g.vertex} : Repr (HamiltonianPath g u v) where
  reprPrec p n := reprPrec p.path n

instance {g : Graph} : Repr ((u v : g.vertex ) ×' HamiltonianPath g u v) where
  reprPrec p n := reprPrec p.2.2.path n

def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (w : g.vertex), List.contains c.cycle.vertices w

class HamiltonianCycle (g : Graph) (u : g.vertex) where
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

instance {g : Graph} {u : g.vertex} : Repr (HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex ) ×' HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.2.cycle n

class HamiltonianGraph (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  is_hamiltonian : cycle.isHamiltonian = true

def Graph.isNonHamiltonian {g : Graph} : Prop := ¬ ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian
def Graph.isNonHamiltonian' {g : Graph} : Prop := ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

end HoG
