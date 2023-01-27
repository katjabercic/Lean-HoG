import TreeSet

namespace TreeMap

open TreeSet
open Bounded

inductive Smap (α β: Type) [LinearOrder α] : ∀ {low high : Bounded α}, low < high → Type
| empty : ∀ {low high} (p : low < high), Smap α β p
| leaf : ∀ {low high} (key : α) (val : β) (lowx : low < element key) (xhigh : element key < high), Smap α β (lt_trans lowx xhigh)
| node : ∀ {low high} (key : α) (val : β) {q : low < element key} {r : element key < high}
           (left : Smap α β q) (right : Smap α β r), Smap α β (lt_trans q r)

-- example : Smap ℕ ℕ (by { trivial } : bottom < top) :=
--   Smap.node 1 10
--     (Smap.leaf 0 666 (by trivial) (by obviously))
--     (Smap.leaf 2 20 (by obviously) (by trivial))

@[reducible]
def Smap.containsKey {α β: Type} [LinearOrder α] (key : α) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Bool
| low, high, p, (Smap.empty _) => false
| low, high, p, (Smap.leaf x _ _ _) => (key = x)
| low, high, p, (Smap.node x _ left right) =>
    lt_by_cases key x
      (fun _ => Smap.containsKey key left)
      (fun _ => true)
      (fun _ => Smap.containsKey key right)

@[reducible]
def Smap.containsVal {α β: Type} [LinearOrder α] [DecidableEq β] (val : β) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Bool
| low, high, p, (Smap.empty _) => false
| low, high, p, (Smap.leaf _ x _ _) => (val = x)
| low, high, p, (Smap.node _ x left right) => (val = x) || Smap.containsVal val left || Smap.containsVal val right

@[reducible]
def Smap.valAt {α β : Type} [LinearOrder α] (key: α) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Option β
| low, high, p, (Smap.empty _) => none
| low, high, p, (Smap.leaf x val _ _) =>     
    lt_by_cases key x
      (fun _ => none)
      (fun _ => some val)
      (fun _ => none)
| low, high, p, (Smap.node x val left right) =>     
    lt_by_cases key x
      (fun _ => Smap.valAt key left)
      (fun _ => some val)
      (fun _ => Smap.valAt key right)

def Smap.size {α β: Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Smap α β p → ℕ
| low, high, p, (Smap.empty _) => 0
| low, high, p, (Smap.leaf x _ _ _) => 1
| low, high, p, (Smap.node x _ left right) => 1 + Smap.size left + Smap.size right

def Smap.toMap {α β : Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Smap α β p → (α → Option β) :=
  fun t x => Smap.valAt x t

@[reducible]
def Smap.forallKeys {α β : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Smap α β b) , Bool
| _, _, _, (Smap.empty _) => true
| _, _, _, (Smap.leaf key _ _ _)=> Decidable.decide (p key)
| _, _, _, (Smap.node key _ left right) => 
  Decidable.decide (p key) && Smap.forallKeys p left && Smap.forallKeys p right

@[reducible]
def Smap.forall {α β : Type} [LinearOrder α] (p : α × β → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Smap α β b) , Bool
| _, _, _, (Smap.empty _) => true
| _, _, _, (Smap.leaf key val _ _)=> Decidable.decide (p (key, val))
| _, _, _, (Smap.node key val left right) => 
  Decidable.decide (p (key, val)) && Smap.forall p left && Smap.forall p right

@[reducible]
def extendProp {β : Type} (p : β → Prop) : Option β → Prop
| none => false
| (some b) => p b

@[reducible]
def OptionProd {α β : Type} : Option α → Option β → Option (α × β)
| none, none => none
| (some a), none => none
| none, (some b) => none
| (some a), (some b) => some (a, b)

@[reducible]
def OptionProdCurried {α β : Type} : Option α × Option β → Option (α × β) := fun ⟨ a, b ⟩ => OptionProd a b

lemma Smap.forall_is_forall {α β : Type} [LinearOrder α] (p : α × β → Prop) [DecidablePred p]:
  ∀ {low high : Bounded α} {b : low < high} (t : Smap α β b), 
  Smap.forall p t = true
  → ∀ (x : α), Smap.containsKey x t
  → (extendProp p) (OptionProdCurried (some x, (Smap.valAt x t))) := by
  intros low high b t
  induction t with
  | empty _ => simp
  | leaf key y _ _ => simp [Smap.forall, Smap.valAt, lt_by_cases, OptionProd, OptionProdCurried]
  | node y _ left right left_ih right_ih =>
    simp [Smap.forall, Smap.valAt]
    intros py lall rall x
    apply lt_by_cases x y
    . intro xy
      simp [Smap.containsKey, lt_by_cases, xy]
      apply left_ih lall
    . intro xy
      simp [Smap.containsKey, lt_by_cases, xy]
      assumption
    . intro yx
      simp [Smap.containsKey, lt_by_cases, yx, lt_asymm]
      tauto
  -- intros low high b t,
  -- induction t with _ _ _ _ _ _ _ _ _ _  _ y B ,
  -- { simp },
  -- { simp [Smap.forall, Smap.val_at, decidable.lt_by_cases, option_prod, option_prod_curried] },
  -- { simp [Smap.forall, Smap.val_at], intros py lall rall x,
  --   apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [ Smap.containsKey, decidable.lt_by_cases, xy], obviously }, -- can we find a better proof that obviously?
  --   { intro xy, simp [ Smap.containsKey, decidable.lt_by_cases, xy], assumption },
  --   { intro yx, simp [ Smap.containsKey, decidable.lt_by_cases, yx, lt_asymm yx], tautology },
  -- }


-- def tmap (α β : Type) [lo : LinearOrder α] := @Smap α β lo bottom top true.intro

-- def tmap.contains_key {α β : Type} [LinearOrder α] (key : α) : tmap α β → Bool := Smap.contains_key key

-- def tmap.contains_val {α β : Type} [LinearOrder α] [decidable_eq β] (val : β) : tmap α β → Bool := Smap.contains_val val

-- def tmap.val_at {α β : Type} [LinearOrder α] (key : α) : tmap α β → option β := Smap.val_at key

-- def tmap.to_map {α β : Type} [LinearOrder α] : tmap α β → (α → option β) := Smap.to_map


end TreeMap