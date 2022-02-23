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

def BT.contains {α : Type} [linear_order α] : BT α → α → bool
| (BT.empty) a := ff
| (BT.leaf b) a := a = b
| (BT.node b left right) a := a = b ∨ if a < b then BT.contains left a else BT.contains right a

structure BST (α : Type) [linear_order α] : Type :=
  (tree : BT α)
  (is_bst : BT.is_bst tree = tt . bool_reflect)

instance lex_repr {α β: Type} [has_repr α] [has_repr β] : has_repr (lex α β) :=
⟨ λ p, "(" ++ has_repr.repr p.fst ++ "," ++ has_repr.repr p.snd ++ ")" ⟩


def BT.edge : BT (lex ℕ ℕ) → ℕ → ℕ → bool
| BT.empty s t := ff
| (BT.leaf ⟨l, r⟩) s t := (l = s ∧ r = t) ∨ (l = t ∧ r = s)
| (BT.node ⟨l, r⟩ left right) s t := (l = s ∧ r = t) ∨ (l = t ∧ r = s) ∨ let p := (min s t, max s t) in
  if p < (l, r) then BT.edge left s t else BT.edge right s t

lemma BT.edge_symm (bt : BT (lex ℕ ℕ)) (s : ℕ) (t : ℕ) : BT.edge bt s t → BT.edge bt t s :=
begin
  intro h,
  cases bt,
    contradiction,
  sorry,
  sorry
end

def BT.neighbors : BT (lex ℕ ℕ) → ℕ → list ℕ
| BT.empty s := []
| (BT.leaf ⟨l, r⟩) s := if l = s then [r] else if r = s then [l] else []
| (BT.node ⟨l, r⟩ left right) s := let nbhds := BT.neighbors left s ++ BT.neighbors right s in
                                    if l = s then r :: nbhds else if r = s then l :: nbhds else nbhds

def BST.neighbors : BST (lex ℕ ℕ) → ℕ → list ℕ := λ bst s, BT.neighbors bst.tree s

def BT.max {α : Type} [linear_order α] [inhabited α] : BT α → α
| BT.empty := inhabited.default α
| (BT.leaf a) := a
| (BT.node a left right) := max a (BT.max right)


def BT.edge_size : BT (lex ℕ ℕ) → ℕ
| BT.empty := 0
| (BT.leaf a) := 2
| (BT.node a left right) := 2 + BT.edge_size left + BT.edge_size right

def BST.edge_size : BST (lex ℕ ℕ) → ℕ := λ bst, BT.edge_size bst.tree