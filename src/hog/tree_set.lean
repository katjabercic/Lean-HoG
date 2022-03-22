import tactic.tauto

inductive bounded (α : Type) : Type
| bottom : bounded
| element : α -> bounded
| top : bounded

open bounded

instance bounded_has_coe (α : Type) : has_coe α (bounded α) :=
  { coe := element }

@[simp, reducible]
def bounded_le {α : Type} [has_le α] : bounded α → bounded α → Prop
  | bottom _ := true
  | (element _) bottom := false
  | (element x) (element y) := (x ≤ y)
  | (element _) top := true
  | top bottom := false
  | top (element _) := false
  | top top := true

instance bounded_has_le (α : Type) [has_le α] : has_le (bounded α) :=
  { le := bounded_le }

@[simp, reducible]
def bounded_lt {α : Type} [has_lt α] : bounded α → bounded α → Prop
  | bottom bottom := false
  | bottom (element _) := true
  | bottom top := true
  | (element _) bottom := false
  | (element x) (element y) := (x < y)
  | (element _) top := true
  | top _ := false

instance bounded_has_lt (α : Type) [has_lt α] : has_lt (bounded α) :=
  { lt := bounded_lt }

lemma bounded_le_trans {α : Type} [preorder α] {a b c : bounded α} :
  bounded_le a b → bounded_le b c → bounded_le a c :=
begin
  cases_matching* (bounded α) ; try { tautology },
  apply le_trans
end

instance bounded_preorder (α : Type) [preorder α] : preorder (bounded α) :=
  { lt := bounded_lt,
    le := bounded_le,
    le_refl := by { intro a, cases a ; trivial },
    le_trans := by { apply bounded_le_trans },
    lt_iff_le_not_le := by { intros a b, cases a ; cases b ; tautology <|>  apply lt_iff_le_not_le }
  }

instance bounded_partial_order (α : Type) [partial_order α]: partial_order (bounded α) :=
  { le_antisymm :=
      by { intros a b,  cases a ; cases b ; try { tautology },
           intros ab ba, congr, apply (le_antisymm ab ba) },
    .. bounded_preorder α }

instance bounded_linear_order (α : Type) [linear_order α] : linear_order (bounded α) :=
  { le_total := by { intros a b, cases a ; cases b ; try { tautology }, apply le_total },
    decidable_le := by { intros a b, cases a ; cases b ; apply_instance },
    .. bounded_partial_order α
  }

def between {α : Type} [has_lt α] (low high : α) := { x : α | low < x ∧ x < high }

inductive search_tree (α : Type) [linear_order α] :
  ∀ {low high : bounded α}, low < high → Type
| empty : ∀ {low high} (p : low < high), search_tree p
| leaf : ∀ {low high} (p : low < high) (x : α), low < element x → element x < high → search_tree p
| node : ∀ {low high} (x : α) (q : low < element x) (r : element x < high)
           (left : search_tree q) (right : search_tree r), search_tree (lt_trans q r)

open search_tree

def elem (α : Type) [linear_order α] (x : α) :
    ∀ {low high : bounded α} {p : low < high}, search_tree α p → bool
| low high p (empty _) := ff
| low high p (leaf _ y _ _) := (x = y)
| low high p (node y q r left right) :=
  order.lt_by_cases
