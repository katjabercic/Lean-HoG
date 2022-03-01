import order.lexicographic
import data.fintype.basic
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

@[reducible]
def BT.contains {α : Type} [linear_order α] : BT α → α → bool
| (BT.empty) a := ff
| (BT.leaf b) a := a = b
| (BT.node b left right) a := a = b ∨ if a < b then BT.contains left a else BT.contains right a

lemma BT.contains_leaf {α : Type} [linear_order α] (t : α) (x : α) : BT.contains (BT.leaf t) x → x = t :=
  sorry

lemma BT.contains_node {α : Type} [linear_order α] (u v : BT α) (x y : α) :
  BT.contains (BT.node y u v) x → (BT.contains u x) ∨ x = y ∨ (BT.contains v x) :=
  sorry

def BT.extension {α : Type} [linear_order α] (t : BT α) : set α := { x : α | BT.contains t x }

#check has_mem

theorem BT.finite {α : Type} [linear_order α] (t : BT α) : set.finite (BT.extension t) :=
begin
  induction t with t x l r IHl IHr,
  { fconstructor, fconstructor, exact ∅, intro x, cases x, contradiction },
  { fconstructor, fconstructor, exact {t}, intro x, cases x with x xp,
    simp, apply BT.contains_leaf, assumption
  }, 
  { sorry  }
end

structure BST (α : Type) [linear_order α] : Type :=
  (tree : BT α)
  (is_bst : BT.is_bst tree = tt . bool_reflect)

instance lex_repr {α β: Type} [has_repr α] [has_repr β] : has_repr (lex α β) :=
⟨ λ p, "(" ++ has_repr.repr p.fst ++ "," ++ has_repr.repr p.snd ++ ")" ⟩

-- The type of edges
structure Edge : Type :=
  (edge : lex ℕ ℕ)
  (src_lt_trg : edge.fst < edge.snd . obviously)

instance Edge_linear_order : linear_order Edge :=
  linear_order.lift (λ (u : Edge), u.edge) (λ u v H, begin cases u, cases v, simp, assumption end)

@[reducible]
def BT.edge (t : BT Edge) (a : ℕ) (b : ℕ) : Prop :=
  decidable.lt_by_cases a b
    (λ _, BT.contains t { edge := (a, b)})
    (λ _, ff)
    (λ _, BT.contains t { edge := (b, a)})

lemma BT.edge_symm (bt : BT Edge) (s : ℕ) (t : ℕ) : BT.edge bt s t → BT.edge bt t s :=
begin
  unfold BT.edge,
  unfold decidable.lt_by_cases,
  cases (lt_trichotomy s t) with p p,
  { simp [p, asymm p] },
  { cases p with p p,
    { simp [p] },
    { simp [p, asymm p] }
  }
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

def BT.neighborhoods : BT (lex ℕ ℕ) → ℕ → list (ℕ × list ℕ) :=
λ tree nodes, list.map (λ (i : ℕ), (i, BT.neighbors tree i)) (list.range nodes)

def BST.neighborhoods : BST (lex ℕ ℕ) → ℕ → list (ℕ × list ℕ) := λ bst n, BT.neighborhoods bst.tree n