import Qq

open Qq

/-- Construct a quoted element of Fin -/
def finOfData (n : Q(Nat)) (k : Nat) : Q(Fin $n) :=
  have k : Q(Nat) := Lean.mkRawNatLit k
  have H : Q(Nat.blt $k $n = true) := (q(Eq.refl true) : Lean.Expr)
  q(Fin.mk $k (Nat.le_of_ble_eq_true $H))
