import .tree_set

namespace tree_map

open tree_set
open tree_set.bounded

inductive smap (α β: Type) [linear_order α] : ∀ {low high : bounded α}, low < high → Type
| empty : ∀ {low high} (p : low < high), smap p
| leaf : ∀ {low high} (key : α) (val : β) (lowx : low < element key) (xhigh : element key < high), smap (lt_trans lowx xhigh)
| node : ∀ {low high} (key : α) (val : β) {q : low < element key} {r : element key < high}
           (left : smap q) (right : smap r), smap (lt_trans q r)

example : smap ℕ ℕ (by { trivial } : bottom < top) :=
  smap.node 1 10
    (smap.leaf 0 666 (by trivial) (by obviously))
    (smap.leaf 2 20 (by obviously) (by trivial))

@[reducible]
def smap.contains_key {α β: Type} [linear_order α] (key : α) :
    ∀ {low high : bounded α} {p : low < high}, smap α β p → bool
| low high p (smap.empty _) := ff
| low high p (smap.leaf x _ _ _) := (key = x)
| low high p (smap.node x _ left right) :=
    decidable.lt_by_cases key x
      (λ _, smap.contains_key left)
      (λ _, tt)
      (λ _, smap.contains_key right)


@[reducible]
def smap.contains_val {α β: Type} [linear_order α] [decidable_eq β] (val : β) :
    ∀ {low high : bounded α} {p : low < high}, smap α β p → bool
| low high p (smap.empty _) := ff
| low high p (smap.leaf _ x _ _) := (val = x)
| low high p (smap.node _ x left right) := (val = x) || smap.contains_val left || smap.contains_val right

@[reducible]
def smap.val_at {α β : Type} [linear_order α] (key: α) :
    ∀ {low high : bounded α} {p : low < high}, smap α β p → option β
| low high p (smap.empty _) := none
| low high p (smap.leaf x val _ _) :=     
    decidable.lt_by_cases key x
      (λ _, none)
      (λ _, some val)
      (λ _, none)
| low high p (smap.node x val left right) :=     
    decidable.lt_by_cases key x
      (λ _, smap.val_at left)
      (λ _, some val)
      (λ _, smap.val_at right)

def smap.size {α β: Type} [linear_order α] : ∀ {low high : bounded α} {p : low < high}, smap α β p → ℕ
| low high p (smap.empty _) := 0
| low high p (smap.leaf x _ _ _) := 1
| low high p (smap.node x _ left right) := 1 + smap.size left + smap.size right

def smap.to_map {α β : Type} [linear_order α] :
  ∀ {low high : bounded α} {p : low < high}, 
  smap α β p → (α → option β) 
:=
λ low high p t x, smap.val_at x t

@[reducible]
def smap.forall_keys {α β : Type} [linear_order α] (p : α → Prop) [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b) , bool
| _ _ _ (smap.empty _) := tt
| _ _ _ (smap.leaf key _ _ _):= decidable.to_bool (p key)
| _ _ _ (smap.node key _ left right) := 
  decidable.to_bool (p key) && smap.forall_keys left && smap.forall_keys right


@[reducible]
def smap.forall {α β : Type} [linear_order α] (p : α × β → Prop) [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b) , bool
| _ _ _ (smap.empty _) := tt
| _ _ _ (smap.leaf key val _ _):= decidable.to_bool (p (key, val))
| _ _ _ (smap.node key val left right) := 
  decidable.to_bool (p (key, val)) && smap.forall left && smap.forall right

@[reducible]
def extend_prop {β : Type} (p : β → Prop) : option β → Prop
| none := false
| (some b) := p b

@[reducible]
def option_prod {α β : Type} : option α → option β → option (α × β)
| none none := none
| (some a) none := none
| none (some b) := none
| (some a) (some b) := some (a, b)

@[reducible]
def option_prod_curried {α β : Type} : option α × option β → option (α × β) := λ ⟨ a, b ⟩, option_prod a b

lemma smap.forall_is_forall {α β : Type} [linear_order α] (p : α × β → Prop) [decidable_pred p]:
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b), 
  smap.forall p t = tt 
  → ∀ (x : α), smap.contains_key x t 
  → (extend_prop p) (option_prod_curried (some x, (smap.val_at x t))) :=
begin
  intros low high b t,
  induction t with _ _ _ _ _ _ _ _ _ _  _ y B ,
  { simp },
  { simp [smap.forall, smap.val_at, decidable.lt_by_cases, option_prod, option_prod_curried] },
  { simp [smap.forall, smap.val_at], intros py lall rall x,
    apply (decidable.lt_by_cases x y),
    { intro xy, simp [ smap.contains_key, decidable.lt_by_cases, xy], obviously }, -- can we find a better proof that obviously?
    { intro xy, simp [ smap.contains_key, decidable.lt_by_cases, xy], assumption },
    { intro yx, simp [ smap.contains_key, decidable.lt_by_cases, yx, lt_asymm yx], tautology },
  }
end

def tmap (α β : Type) [lo : linear_order α] := @smap α β lo bottom top true.intro

def tmap.contains_key {α β : Type} [linear_order α] (key : α) : tmap α β → bool := smap.contains_key key

def tmap.contains_val {α β : Type} [linear_order α] [decidable_eq β] (val : β) : tmap α β → bool := smap.contains_val val

def tmap.val_at {α β : Type} [linear_order α] (key : α) : tmap α β → option β := smap.val_at key

def tmap.to_map {α β : Type} [linear_order α] : tmap α β → (α → option β) := smap.to_map


end tree_map