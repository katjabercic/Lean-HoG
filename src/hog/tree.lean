import order.lexicographic
import .tactic

universe u

inductive BT (α : Type) [linear_order α] : Type
| empty : BT
| leaf : α → BT
| node : α → BT → BT → BT

def BT.to_string {α : Type} [linear_order α] [has_repr α] : BT α → string
| BT.empty := "_"
| (BT.leaf a) := has_repr.repr a
| (BT.node a left right) := has_repr.repr a ++ "--" ++ BT.to_string right ++ "\n   \\--" ++ BT.to_string left

instance BT_repr {α : Type} [linear_order α] [has_repr α] : has_repr (BT α) := ⟨ BT.to_string ⟩ 

def BT.values {α : Type} [linear_order α] : BT α → list α
| BT.empty := []
| (BT.leaf a) := [a]
| (BT.node a left right) := BT.values left ++ [a] ++ BT.values right

def BT.is_bst {α : Type} [linear_order α] : BT α → bool
| BT.empty := tt
| (BT.leaf a) := tt
| (BT.node a left right) := list.all (BT.values left) (λ x, x < a) ∧ list.all (BT.values right) (λ x, x > a)

def BT.contains {α : Type} [linear_order α] : α → BT α → bool
| a (BT.empty) := ff
| a (BT.leaf b) := a = b
| a (BT.node b left right) := a = b ∨ if a < b then BT.contains a left else BT.contains a right

-- def BT.construct {α : Type} [linear_order α] : list α → BT α
-- | [] := BT.empty
-- | (a :: as) := sorry

structure BST (α : Type) [linear_order α] : Type :=
  (tree : BT α)
  (is_bst : BT.is_bst tree = tt . bool_reflect)

-- instance lex_repr {α β: Type} [has_repr α] [has_repr β] : has_repr (lex α β) :=
-- ⟨ λ p, "(" ++ has_repr.repr p.fst ++ "," ++ has_repr.repr p.snd ++ ")" ⟩ 

-- def cycle3_tree : BT (lex ℕ ℕ) := BT.node (2,1) (BT.leaf (1,3)) (BT.leaf (3,4))

-- #eval BT.is_bst cycle3_tree

-- def G1 : BT (lex ℕ ℕ) := BT.node (1,4) (BT.node (1,3) (BT.leaf (1,2)) BT.empty) (BT.node (2,3) BT.empty (BT.leaf (3,4)))
-- def G2 : BT (lex ℕ ℕ) := BT.node (1, 4) (BT.node (1, 3) (BT.leaf (1, 2)) (BT.empty)) (BT.node (3, 4) (BT.leaf (2, 3)) (BT.empty))


-- def G1_bst : BST (lex ℕ ℕ) :=
-- { tree := BT.node (1,4) (BT.node (1,3) (BT.leaf (1,2)) BT.empty) (BT.node (2,3) BT.empty (BT.leaf (3,4))),
--   is_bst := by bool_reflect
-- }