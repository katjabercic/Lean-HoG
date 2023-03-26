import TreeSet

namespace TreeMap

open TreeSet
open Bounded

inductive Smap (α β: Type) [LinearOrder α] : ∀ {low high : Bounded α}, low < high → Type
| empty : ∀ {low high} (p : low < high), Smap α β p
| leaf : ∀ {low high} (key : α) (_ : β) (lowx : low < element key) (xhigh : element key < high), Smap α β (lt_trans lowx xhigh)
| node : ∀ {low high} (key : α) (_ : β) {q : low < element key} {r : element key < high}
           (_ : Smap α β q) (_ : Smap α β r), Smap α β (lt_trans q r)

-- example : Smap ℕ ℕ (by { trivial } : bottom < top) :=
--   Smap.node 1 10
--     (Smap.leaf 0 666 (by trivial) (by obviously))
--     (Smap.leaf 2 20 (by obviously) (by trivial))

@[reducible]
def Smap.containsKey {α β: Type} [LinearOrder α] (key : α) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Bool
| _, _, _, (Smap.empty _) => false
| _, _, _, (Smap.leaf x _ _ _) => (key = x)
| _, _, _, (Smap.node x _ left right) =>
    lt_by_cases key x
      (fun _ => Smap.containsKey key left)
      (fun _ => true)
      (fun _ => Smap.containsKey key right)

@[reducible]
def Smap.containsVal {α β: Type} [LinearOrder α] [DecidableEq β] (val : β) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Bool
| _, _, _, (Smap.empty _) => false
| _, _, _, (Smap.leaf _ x _ _) => (val = x)
| _, _, _, (Smap.node _ x left right) => (val = x) || Smap.containsVal val left || Smap.containsVal val right

@[reducible]
def Smap.valAt {α β : Type} [LinearOrder α] (key: α) :
    ∀ {low high : Bounded α} {p : low < high}, Smap α β p → Option β
| _, _, _, (Smap.empty _) => none
| _, _, _, (Smap.leaf x val _ _) =>     
    lt_by_cases key x
      (fun _ => none)
      (fun _ => some val)
      (fun _ => none)
| _, _, _, (Smap.node x val left right) =>     
    lt_by_cases key x
      (fun _ => Smap.valAt key left)
      (fun _ => some val)
      (fun _ => Smap.valAt key right)

def Smap.size {α β: Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Smap α β p → ℕ
| _, _, _, (Smap.empty _) => 0
| _, _, _, (Smap.leaf _ _ _ _) => 1
| _, _, _, (Smap.node _ _ left right) => 1 + Smap.size left + Smap.size right

def Smap.toMap {α β : Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Smap α β p → (α → Option β) :=
  fun t x => Smap.valAt x t

@[reducible]
def Smap.forallKeys {α β : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (_ : Smap α β b) , Bool
| _, _, _, (Smap.empty _) => true
| _, _, _, (Smap.leaf key _ _ _)=> Decidable.decide (p key)
| _, _, _, (Smap.node key _ left right) => 
  Decidable.decide (p key) && Smap.forallKeys p left && Smap.forallKeys p right

@[reducible]
def Smap.forall {α β : Type} [LinearOrder α] (p : α × β → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (_ : Smap α β b) , Bool
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
| (some _), none => none
| none, (some _) => none
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

def Smap.max? {α β: Type} [LinearOrder α] [LinearOrder β] {low high : Bounded α} {p : low < high} : Smap α β p → Option β
  | Smap.empty _ => none
  | Smap.leaf _ val _ _ => some val
  | Smap.node _ val left right =>
    match left.max?, right.max? with
    | none, none => val
    | some x, none => if val < x then x else val
    | none, some y => if val < y then y else val
    | some x, some y => if val < x then (if y < x then x else y) else (if val < y then y else val)

def Smap.maxD {α β: Type} [LinearOrder α] [LinearOrder β] {low high : Bounded α} {p : low < high} (default : β) :
  Smap α β p → β
  | Smap.empty _ => default
  | Smap.leaf _ val _ _ => val
  | Smap.node _ val left right =>
    match left.max?, right.max? with
    | none, none => val
    | some x, none => if val < x then x else val
    | none, some y => if val < y then y else val
    | some x, some y => if val < x then (if y < x then x else y) else (if val < y then y else val)

def Smap.min? {α β: Type} [LinearOrder α] [LinearOrder β] {low high : Bounded α} {p : low < high} : Smap α β p → Option β
  | Smap.empty _ => none
  | Smap.leaf _ val _ _ => some val
  | Smap.node _ val left right =>
    match left.min?, right.min? with
    | none, none => val
    | some x, none => if val > x then x else val
    | none, some y => if val > y then y else val
    | some x, some y => if val > x then (if y > x then x else y) else (if val > y then y else val)

def Smap.minD {α β: Type} [LinearOrder α] [LinearOrder β] {low high : Bounded α} {p : low < high} (default : β) :
  Smap α β p → β
  | Smap.empty _ => default
  | Smap.leaf _ val _ _ => val
  | Smap.node _ val left right =>
    match left.max?, right.max? with
    | none, none => val
    | some x, none => if val > x then x else val
    | none, some y => if val > y then y else val
    | some x, some y => if val > x then (if y > x then x else y) else (if val > y then y else val)


def Smap.map {α β γ: Type} [LinearOrder α] {low high : Bounded α} {p : low < high} : Smap α β p → (β → γ) → Smap α γ p
  | Smap.empty _, _ => Smap.empty _
  | Smap.leaf key val lowKey keyHigh, f => Smap.leaf key (f val) lowKey keyHigh
  | Smap.node key val left right, f => Smap.node key (f val) (left.map f) (right.map f)

-- ================================================================================
--                          Tmap
-- ================================================================================

def Tmap (α β : Type) [lo : LinearOrder α] := @Smap α β lo bottom top (by rfl)

def Tmap.containsKey {α β : Type} [LinearOrder α] (key : α) : Tmap α β → Bool := Smap.containsKey key

def Tmap.containsVal {α β : Type} [LinearOrder α] [DecidableEq β] (val : β) : Tmap α β → Bool := Smap.containsVal val

def Tmap.valAt {α β : Type} [LinearOrder α] (key : α) : Tmap α β → Option β := Smap.valAt key

def Tmap.toMap {α β : Type} [LinearOrder α] : Tmap α β → (α → Option β) := Smap.toMap

def Tmap.max? {α β : Type} [LinearOrder α] [LinearOrder β] : Tmap α β → Option β := Smap.max?

def Tmap.maxD {α β: Type} [LinearOrder α] [LinearOrder β] (default : β) : Tmap α β → β := Smap.maxD default

def Tmap.min? {α β : Type} [LinearOrder α] [LinearOrder β] : Tmap α β → Option β := Smap.min?

def Tmap.minD {α β: Type} [LinearOrder α] [LinearOrder β] (default : β) : Tmap α β → β := Smap.minD default

def Tmap.map {α β γ: Type} [LinearOrder α] : Tmap α β → (β → γ) → Tmap α γ := Smap.map

end TreeMap