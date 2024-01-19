import HoG.Graph
import HoG.Walk

namespace HoG

@[simp]
def Path.isHamiltonian {g : Graph} {u v : g.vertex} (p : Path g u v) : Bool :=
  ∀ (w : g.vertex), List.contains p.walk.vertices w

class HamiltonianPath (g : Graph) (u v : g.vertex) where
  path : Path g u v
  isHamiltonian : path.isHamiltonian = true

instance {g : Graph} {u v : g.vertex} : Repr (HamiltonianPath g u v) where
  reprPrec p n := reprPrec p.path n

instance {g : Graph} : Repr ((u v : g.vertex ) ×' HamiltonianPath g u v) where
  reprPrec p n := reprPrec p.2.2.path n

@[simp]
def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (v : g.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (g : Graph) (u : g.vertex) where
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

instance {g : Graph} {u : g.vertex} : Repr (HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex ) ×' HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.2.cycle n

@[simp]
def Graph.isHamiltonian (g : Graph) : Prop :=
  ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian

class HamiltonianGraph (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

@[simp]
def Graph.isNonHamiltonian (g : Graph) : Prop := ¬ g.isHamiltonian

@[simp]
def Graph.isNonHamiltonian' {g : Graph} : Prop := ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

theorem equivNonHamiltonianDefs (g : Graph) :
  g.isNonHamiltonian ↔ g.isNonHamiltonian' :=
  by simp

end HoG
