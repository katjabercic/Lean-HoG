inductive T (α : Type) [linear_order α] : ℕ → Type 
| NodeR (n : ℕ) : α → T n → T (n+1) → T n
| NodeL (n : ℕ) : α → T (n+1) → T n → T n
| Node (n : ℕ) : α → T n → T n → T n

inductive rb_tree (α : Type) [linear_order α] : ℕ → Type
| Branch (n : ℕ) : T α n → rb_tree (n+1)
| Leaf : rb_tree 0


