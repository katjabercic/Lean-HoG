import Mathlib.Order.Synonym

-- The type of edges
structure edge : Type :=
  (edge : Lex (Nat × Nat))
  (src_lt_trg : edge.fst < edge.snd)