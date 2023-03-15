import Mathlib.Data.Prod.Lex

structure Pair : Type :=
  (pair : Lex (Nat × Nat))

instance PairLinearOrder : LinearOrder Pair := 
  LinearOrder.lift' (fun (u : Pair) => u.pair) (fun u v H => by cases u; cases v; simp; assumption)

set_option pp.explicit true in
instance comparePairDecidable (p1 p2 : Pair) : Decidable (p1 < p2) := by
  have l : LinearOrder Pair := by apply PairLinearOrder
  have r := l.decidable_lt
  have q := r p1 p2
  simp at q
  exact q