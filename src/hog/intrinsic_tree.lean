import tactic

inductive bst (α : Type) [linear_order α] : α → α → Type
| empty (e : α) : bst e e
| leaf (l u : α) (x : α) : l ≤ x ∧ x ≤ u → bst l u
| node (l₁ u₁ l₂ u₂ : α) (x : α) (left : bst l₁ u₁) (right : bst l₂ u₂) : u₁ < x ∧ x < l₂ → bst l₁ u₂


-- def bst.to_string {α : Type} [linear_order α] [has_repr α] (l u : α) : bst α l u → string
-- | (bst.empty l u cond) := "_"
-- | (bst.leaf l u x cond) := has_repr.repr x
-- | (bst.node l₁ u₁ l₂ u₂ x left right cond) := has_repr.repr x ++ "--" ++ bst.to_string right ++ "\n   \\--" ++ bst.to_string left

@[reducible]
def bst.values {α : Type} [linear_order α] : Π (l u : α), bst α l u → list α
| l u (bst.empty e) := []
| l u (bst.leaf min max x cond) := [x]
| l u (bst.node l₁ u₁ l₂ u₂ x left right cond) := bst.values l₁ u₁ left ++ [x] ++ bst.values l₂ u₂ right


def t : bst ℕ 0 2 := bst.leaf 0 2 1 (by simp)

#check bst.values t