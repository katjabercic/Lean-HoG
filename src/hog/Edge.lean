import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.Basic
import TreeSet
import OrdEq
import Mathlib.Data.Sigma.Order

namespace HoG

@[reducible]
def Edge (m : Nat) := Lex ((k : Fin m) × Fin k)

@[reducible]
def Edge.mk {m : Nat} (i : Fin m) (j : Fin i) : Edge m := Sigma.mk i j

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a n = true) (H2 : Nat.blt b a = true) : Edge n :=
  ⟨⟨a, Nat.le_of_ble_eq_true H1⟩, ⟨b, Nat.le_of_ble_eq_true H2⟩⟩

-- Get rid of this stuff once the above "deriving Fintype" works
def Graph.edgeEquiv (vertexSize : Nat) : (fst : Fin vertexSize) × Fin fst ≃ Edge vertexSize where
  toFun z := ⟨z.1, z.2⟩
  invFun c := ⟨c.fst, c.snd⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance Edge_Fintype (vertexSize : Nat): Fintype (Edge vertexSize) :=
  Fintype.ofEquiv _ (Graph.edgeEquiv vertexSize)

end HoG