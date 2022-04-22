import order.lexicographic
import data.fintype.basic
import tactic
-- Extension of an order with a new bottom and top elements. 
namespace tree_set

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
    .. tree_set.bounded_preorder α }

instance bounded_linear_order (α : Type) [linear_order α] : linear_order (bounded α) :=
  { le_total := by { intros a b, cases a ; cases b ; try { tautology }, apply le_total },
    decidable_le := by { intros a b, cases a ; cases b ; apply_instance },
    .. tree_set.bounded_partial_order α
  }

inductive stree (α : Type) [linear_order α] : ∀ {low high : bounded α}, low < high → Type
| empty : ∀ {low high} (p : low < high), stree p
| leaf : ∀ {low high} (x : α) (lowx : low < element x) (xhigh : element x < high), stree (lt_trans lowx xhigh)
| node : ∀ {low high} (x : α) {q : low < element x} {r : element x < high}
           (left : stree q) (right : stree r), stree (lt_trans q r)

example: stree ℕ (by { trivial } : bottom < top) :=
  stree.node 20 
    (stree.empty true.intro)
    (stree.leaf 42 (by { norm_num } : 20 < 42) true.intro)

@[reducible]
def stree.elem {α : Type} [linear_order α] (x : α) :
    ∀ {low high : bounded α} {p : low < high}, stree α p → bool
| low high p (stree.empty _) := ff
| low high p (stree.leaf y _ _) := (x = y)
| low high p (stree.node y left right) :=
    decidable.lt_by_cases x y
      (λ _, stree.elem left)
      (λ _, tt)
      (λ _, stree.elem right)

def stree.size {α : Type} [linear_order α] : ∀ {low high : bounded α} {p : low < high}, stree α p → ℕ
| low high p (stree.empty _) := 0
| low high p (stree.leaf x _ _) := 1
| low high p (stree.node x left right) := 1 + stree.size left + stree.size right

theorem stree.elem_low {α : Type} [linear_order α] (x : α)
  {low high : bounded α} {p : low < high} (t : stree α p) :
  stree.elem x t = tt → low < element x :=
begin
  induction t with _ _ _ _ _ _ _ _ _ _ y,
  { obviously },
  { obviously },
  { apply (decidable.lt_by_cases x y),
    { intro xy, simp [stree.elem, decidable.lt_by_cases, xy], obviously },
    { intro xy, obviously },
    { intro yx, simp [stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], intro, transitivity' y, obviously }
  }
end

theorem stree.elem_high {α : Type} [linear_order α] (x : α)
  {low high : bounded α} {p : low < high} (t : stree α p) :
  stree.elem x t = tt → element x < high :=
begin
  induction t with _ _ _ A B C D E low high y I J left right ih_right ih_left,
  { obviously },
  { obviously },
  { apply (decidable.lt_by_cases x y),
    { intro xy, simp [stree.elem, decidable.lt_by_cases, xy], intro, transitivity' y, obviously },
    { intro xy, obviously },
    { intro yx, simp [stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], obviously }
  }
end

@[reducible]
def stree.insert {α : Type} [linear_order α] (x : α) :
  ∀ {low high : bounded α} {p : low < high} (t : stree α p), low < element x → element x < high → stree α p
| low high p (stree.empty _) lowx xhigh := stree.leaf x lowx xhigh
| low high p (stree.leaf y lowy yhigh) lowx xhigh :=
    decidable.lt_by_cases x y
      (λ xy, stree.node y (stree.leaf x lowx xy) (stree.empty yhigh))
      (λ _, stree.leaf y lowy yhigh)
      (λ yx, stree.node y (stree.empty lowy) (stree.leaf x yx xhigh))
| low high p (stree.node y left right) lowx xhigh :=
    decidable.lt_by_cases x y
      (λ xy, stree.node y (@stree.insert _ y _ left lowx xy) right)
      (λ _, stree.node y left right)
      (λ yx, stree.node y left (@stree.insert y _ _ right yx xhigh))

lemma elem_insert (α : Type) [linear_order α] (x : α) {low high : bounded α}
  {lowx : low < element x} {xhigh : element x < high} (t : stree α (lt_trans lowx xhigh)) :
  stree.elem x (stree.insert x t lowx xhigh) :=
begin
  induction t with _ _ _ _ _ y _ _ _ _ y _ _ _ _ ih_left ih_right,
  { simp },
  { apply (decidable.lt_by_cases x y),
    { intro xy, simp [stree.elem, stree.insert, decidable.lt_by_cases, xy] },
    { intro xy, simp [stree.elem, stree.insert, decidable.lt_by_cases, xy] },
    { intro yx, simp [stree.elem, stree.insert, decidable.lt_by_cases, lt_asymm, yx] }
  },
  { apply (decidable.lt_by_cases x y),
    { intro xy, simp [stree.elem, stree.insert, decidable.lt_by_cases, xy], apply ih_left },
    { intro xy, simp [stree.elem, stree.insert, decidable.lt_by_cases, xy, lt_irrefl] },
    { intro yx, simp [stree.elem, stree.insert, decidable.lt_by_cases, lt_asymm, yx], apply ih_right }
  } 
end

@[reducible]
def stree.forall {α : Type} [linear_order α] (p : α → Prop) [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} (t : stree α b) , bool
| _ _ _ (stree.empty _) := tt
| _ _ _ (stree.leaf x _ _):= decidable.to_bool (p x)
| _ _ _ (stree.node x left right) := 
  decidable.to_bool (p x) && stree.forall left && stree.forall right

lemma stree.forall_is_forall {α : Type} [linear_order α] (p : α → Prop) [decidable_pred p]:
  ∀ {low high : bounded α} {b : low < high} (t : stree α b), 
  stree.forall p t = tt → ∀ (x : α), stree.elem x t → p x :=  
begin
  intros low high b t,
  induction t with _ _ _ _ _ _ _ _ _ _  y,
  { simp },
  { simp [stree.forall] },
  { simp [stree.forall], intros py lall rall x,
    apply (decidable.lt_by_cases x y),
    { intro xy, simp [ stree.elem, decidable.lt_by_cases, xy], tautology },
    { intro xy, simp [ stree.elem, decidable.lt_by_cases, xy], assumption },
    { intro yx, simp [ stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], tautology },
  }
end

@[reducible]
def stree.exists {α : Type} [linear_order α] :
  ∀ {low high : bounded α} {b : low < high} (t : stree α b) (p : α → bool), bool
| _ _ _ (stree.empty _) _ := ff
| _ _ _ (stree.leaf x _ _) p := p x
| _ _ _ (stree.node x left right) p := p x || stree.exists left p || stree.exists right p

lemma stree.exists_is_exists {α : Type} [linear_order α] (p : α → bool) :
  ∀ {low high : bounded α} {b : low < high} (t : stree α b), 
  stree.exists t p = tt → ∃ (x : α), stree.elem x t ∧ p x :=  
begin
  intros low high b t,
  induction t with low high lh D E F G H I J y L M left right ih_left ih_right,
  { simp [stree.exists] },
  { simp [stree.exists] },
  { simp, intro h, cases h with h1 ept,
    { cases h1 with pyt ept, 
      { existsi y, simp [pyt, stree.elem, decidable.lt_by_cases] },
      { obtain ⟨z, zleft, pz⟩ := ih_left ept,
        existsi z,
        have zy : z < y := stree.elem_high z left zleft,
        simp [stree.elem, decidable.lt_by_cases, zy], tautology
      }
    },
    { obtain ⟨z, zright, pz⟩ := ih_right ept,
      existsi z,
      have yz : y < z := stree.elem_low z right zright,
      simp [stree.elem, decidable.lt_by_cases, yz, lt_asymm yz], tautology }
  }
end

-- def stree.intersection {α : Type} [linear_order α] :
--   ∀ {low high : bounded α} {b : low < high},
--   stree α b → stree α b → stree α b
-- | _ _ b (stree.empty _) t := stree.empty b
-- | _ _ b t (stree.empty _) := stree.empty b
-- | _ _ b (stree.leaf x _ _) (stree.leaf y _ _) := if x = y then (stree.leaf x _ _) else stree.empty b
-- | _ _ b (stree.node x left right) (stree.leaf y _ _) := 
--     if x = y then (stree.leaf x _ _) 
--     else if stree.elem y left then (stree.leaf y _ _)
--     else if stree.elem y right then (stree.leaf y _ _)
--     else stree.empty b
-- | _ _ b (stree.leaf x _ _) (stree.node y left right) :=
--     if x = y then (stree.leaf x _ _) 
--     else if stree.elem x left then (stree.leaf x _ _)
--     else if stree.elem x right then (stree.leaf x _ _)
--     else stree.empty b
-- | _ _ b (stree.node x left right) t :=  sorry

def tset (α : Type) [lo : linear_order α] := @stree α lo bottom top true.intro

def tset.mem {α : Type} [linear_order α] (x : α) (t : tset α) := stree.elem x t

def tset.option_mem {α : Type} [linear_order α] (x : α) : option (tset α) → bool
| none := ff
| (some t) := tset.mem x t


instance tset.has_mem {α : Type} [linear_order α]: has_mem α (tset α) :=
  { mem := λ x t, tset.mem x t }

instance tset.option_has_mem {α : Type} [linear_order α] : has_mem α (option (tset α)) :=
  { mem := λ x t, tset.option_mem x t }

instance tset.has_insert {α : Type} [linear_order α]: has_insert α (tset α) :=
  { insert := λ x t, stree.insert x t true.intro true.intro }

def tset.add {α : Type} [linear_order α] (x : α) (t : tset α) := stree.insert x t true.intro true.intro

lemma tset.forall_is_forall {α : Type} [linear_order α] (p : α → Prop) [decidable_pred p]:
  ∀ (t : tset α), stree.forall p t = tt → ∀ (x : α), x ∈ t → p x :=
  by apply stree.forall_is_forall

def tset.intersection {α : Type} [linear_order α] : tset α → tset α → tset α := sorry

-- The type of edges
structure Edge : Type :=
  (edge : lex ℕ ℕ)
  (src_lt_trg : edge.fst < edge.snd . obviously)

instance Edge_linear_order : linear_order Edge :=
  linear_order.lift (λ (u : Edge), u.edge) (λ u v H, begin cases u, cases v, simp, assumption end)

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
def smap.forall {α β : Type} [linear_order α] (p : β → Prop) [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b) , bool
| _ _ _ (smap.empty _) := tt
| _ _ _ (smap.leaf _ val _ _):= decidable.to_bool (p val)
| _ _ _ (smap.node _ val left right) := 
  decidable.to_bool (p val) && smap.forall left && smap.forall right

@[reducible]
def extend_prop {β : Type} (p : β → Prop) : option β → Prop
| none := false
| (some b) := p b


lemma smap.forall_is_forall {α β : Type} [linear_order α] (p : β → Prop) [decidable_pred p]:
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b), 
  smap.forall p t = tt → ∀ (x : α), smap.contains_key x t → (extend_prop p) (smap.val_at x t) :=  
begin
  intros low high b t,
  induction t with _ _ _ _ _ _ _ _ _ _  _ y B ,
  { simp },
  { simp [smap.forall, smap.val_at, decidable.lt_by_cases] },
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

end tree_set