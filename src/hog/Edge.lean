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

end HoG
