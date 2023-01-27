import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Tauto
import Mathlib.Mathport.Syntax
import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import Init.Core
import Init.Prelude

namespace TreeSet

inductive Bounded (α : Type) : Type
  | bottom : Bounded α 
  | element : α -> Bounded α 
  | top : Bounded α 

open Bounded

instance BoundedHasCoe (α : Type) : Coe α (Bounded α) where
  coe x := .element x

@[simp, reducible]
def Bounded_le {α : Type} [LE α] : Bounded α → Bounded α → Prop
  | bottom, _ => true
  | (element _), bottom => false
  | (element x), (element y) => (x ≤ y)
  | (element _), top => true
  | top, bottom => false
  | top, (element _) => false
  | top, top => true
  
instance Bounded_has_le (α : Type) [LE α] : LE (Bounded α) where
  le := Bounded_le

@[simp, reducible]
def Bounded_lt {α : Type} [LT α] : Bounded α → Bounded α → Prop
  | bottom, bottom => false
  | bottom, (element _) => true
  | bottom, top => true
  | (element _), bottom => false
  | (element x), (element y) => (x < y)
  | (element _), top => true
  | top, _ => false

instance Bounded_has_lt (α : Type) [LT α] : LT (Bounded α) where
  lt := Bounded_lt

theorem Bounded_le_trans {α : Type} [Preorder α] {a b c : Bounded α} :
  Bounded_le a b → Bounded_le b c → Bounded_le a c := by
  intros a_le_b b_le_c
  match a, b with
  | bottom, _ => trivial
  | element x, bottom => contradiction
  | element x, element y => {
    match c with
    | bottom => contradiction
    | element z =>
      simp at a_le_b
      simp at b_le_c
      have h : x ≤ z := by apply le_trans a_le_b b_le_c
      simp [h]
    | top => rfl
  }
  | element x, top => 
    match c with
    | bottom => contradiction
    | element y => contradiction
    | top => rfl
  | top, top =>
    match c with
    | bottom => contradiction
    | element y => contradiction
    | top => rfl


instance Bounded_preorder (α : Type) [Preorder α] : Preorder (Bounded α) where
  lt := Bounded_lt
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intros a b c; apply Bounded_le_trans
  lt_iff_le_not_le := by 
    intros a b; cases a <;> repeat (first | cases b | tauto | apply lt_iff_le_not_le)

instance Bounded_partial_order (α : Type) [PartialOrder α]: PartialOrder (Bounded α) where
  le_antisymm := by
    intros a b h h'
    cases a <;> repeat (first | cases b | rfl | contradiction | simp; apply le_antisymm <;> assumption)

lemma foo (a : α) [LinearOrder α] : bottom ≤ (element a) := by
  rfl

lemma foo' (a b : α) [LinearOrder α] : Decidable (element a ≤ element b) := by
  apply decidable_of_iff (a ≤ b)
  apply Iff.intro <;> (intro h; assumption)

noncomputable instance Bounded_linear_order (α : Type) [LinearOrder α] : LinearOrder (Bounded α) where
  le_total := by
    intros a b
    cases a <;> cases b <;> tauto
    apply le_total
  decidable_le := by
    intros a b
    cases a <;> cases b <;> simp <;>
    (first 
      | apply instDecidableTrue 
      | apply decidable_of_iff True; simp; rfl
      | apply decidable_of_iff False ; simp; by_contra; contradiction
      | apply foo'
    )

-- Definition of binary search tree
inductive Stree (α : Type) [LinearOrder α] : ∀ {low high : Bounded α}, low < high → Type
  | empty : ∀ {low high} (p : low < high), Stree α p
  | leaf : ∀ {low high} (x : α) (lowx : low < element x) (xhigh : element x < high), Stree α (lt_trans lowx xhigh)
  | node : ∀ {low high} (x : α) {q : low < element x} {r : element x < high}
             (left : Stree α q) (right : Stree α r), Stree α (lt_trans q r)

lemma fou : 20 < 42 := by
  simp

lemma fuu : @LT.lt (Bounded Nat) (@Bounded_has_lt Nat Preorder.toLT) (element 20) (element 42) := by
  have h : 20 < 42 := fou
  assumption

-- example: @Stree Nat (_) (bottom) (top) h :=
--   Stree.node 20
--     (Stree.empty (by rfl))
--     (Stree.leaf 42 (fuu) (by {  }))

@[reducible]
def Stree.elem {α : Type} [LinearOrder α] (x : α) :
    ∀ {low high : Bounded α} {p : low < high}, Stree α p → Bool
  | _, _, _, (Stree.empty _) => false
  | _, _, _, (Stree.leaf y _ _) => (x = y)
  | _, _, _, (Stree.node y left right) => (x = y) || Stree.elem x left || Stree.elem x right

def Stree.size {α : Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Stree α p → Nat
  | low, high, p, (Stree.empty _) => 0
  | low, high, p, (Stree.leaf x _ _) => 1
  | low, high, p, (Stree.node x left right) => 1 + Stree.size left + Stree.size right

theorem Stree.elem_low {α : Type} [LinearOrder α] (x : α)
  {low high : Bounded α} {p : low < high} (t : Stree α p) :
  Stree.elem x t = true → low < element x := by
  induction t with
  | empty _ => intro h; contradiction
  | leaf _ _ _ =>
    intro h
    simp at h
    rw [h]
    assumption
  | node y l r left_ih right_ih =>
    apply @Decidable.byCases (x < y)
    . intro x_less_y
      intro h
      simp at h
      cases h with
      | inl hp =>
        cases hp with
        | inl hpp => rw [hpp]; assumption
        | inr hpq => apply left_ih hpq
      | inr hq =>
        have h' : element y < element x := by apply right_ih hq
        have h'' : y < x := by assumption
        have g : ¬ (y < x) := by apply lt_asymm x_less_y
        contradiction
    . intro _
      intro h
      simp at h
      cases h with
      | inl hp => 
        cases hp with
        | inl hpp => rw [hpp]; assumption
        | inr hpq =>
          apply left_ih hpq
      | inr hq =>
        have h' : element y < element x := by apply right_ih hq
        apply lt_trans' h'
        assumption

theorem Stree.elem_high {α : Type} [LinearOrder α] (x : α)
  {low high : Bounded α} {p : low < high} (t : Stree α p) :
  Stree.elem x t = true → element x < high := by
  intro h
  induction t with
  | empty _ => contradiction
  | leaf _ _ _ => 
    simp at h
    rw [h]
    assumption
  | node y l r left_ih right_ih =>
    simp at h
    cases h with
    | inl hp =>
      cases hp with
      | inl hpp => rw [hpp]; assumption
      | inr hpq =>
        have h' : element x < element y := by apply left_ih hpq
        apply lt_trans h'
        assumption
    | inr hq => apply right_ih hq

#check lt_by_cases

@[reducible]
def Stree.insert {α : Type} [LinearOrder α] (x : α) :
  ∀ {low high : Bounded α} {p : low < high} (t : Stree α p), low < element x → element x < high → Stree α p
  | low, high, p, (Stree.empty _), lowx, xhigh => Stree.leaf x lowx xhigh
  | low, high, p, (Stree.leaf y lowy yhigh), lowx, xhigh =>
    lt_by_cases x y
      (fun xy => Stree.node y (Stree.leaf x lowx xy) (Stree.empty yhigh))
      (fun _ => Stree.leaf y lowy yhigh)
      (fun yx => Stree.node y (Stree.empty lowy) (Stree.leaf x yx xhigh))
  | low, high, p, (Stree.node y left right), lowx, xhigh =>
    lt_by_cases x y
      (fun xy => Stree.node y (@Stree.insert _ _ x _ _ _ left lowx xy) right)
      (fun _ => Stree.node y left right)
      (fun yx => Stree.node y left (@Stree.insert _ _ x _ _ _ right yx xhigh))

theorem elem_insert (α : Type) [LinearOrder α] (x : α) {low high : Bounded α}
  {lowx : low < element x} {xhigh : element x < high} (p : low < high) (t : Stree α p) :
  Stree.elem x (Stree.insert x t lowx xhigh) := by
  induction t with
  | empty _ => simp
  | leaf y _ _ =>
    apply lt_by_cases x y <;> (intro h; simp [Stree.insert, lt_by_cases, h, lt_asymm])
  | node y l r left_ih right_ih =>
    apply lt_by_cases x y <;> intro h <;>
    simp [Stree.insert, lt_by_cases, h, lt_asymm, left_ih, right_ih]

@[reducible]
def Stree.forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), Bool
  | _, _, _, (Stree.empty _) => true
  | _, _, _, (Stree.leaf x _ _) => Decidable.decide (p x)
  | _, _, _, (Stree.node x left right) => 
    Decidable.decide (p x) && Stree.forall p left && Stree.forall p right

def Stree.option_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Option (Stree α b)), Bool
  | _, _, _, none => false
  | _, _, _, (some t) => Stree.forall p t

lemma Stree.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
  Stree.forall p t = true → ∀ (x : α), Stree.elem x t → p x :=  by
  intros low high b t
  induction t with
  | empty _ => simp
  | leaf y _ _ => simp
  | node y l r left_ih right_ih =>
    simp
    intros py lall rall x
    apply lt_by_cases x y <;>
    { intro xy
      intro h
      cases h with
      | inl hp =>
        cases hp with
        | inl hpp => rw [hpp]; exact py
        | inr hpq =>
          apply left_ih lall
          exact hpq
      | inr hq =>
        apply right_ih rall
        exact hq
    }

@[reducible]
def Stree.exists {α : Type} [LinearOrder α] :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b) (p : α → Bool), Bool
  | _, _, _, (Stree.empty _), _ => false
  | _, _, _, (Stree.leaf x _ _), p => p x
  | _, _, _, (Stree.node x left right), p => p x || Stree.exists left p || Stree.exists right p

lemma Stree.exists_is_exists {α : Type} [LinearOrder α] (p : α → Bool) :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
  Stree.exists t p = true → ∃ (x : α), Stree.elem x t ∧ p x := by
  intros low high b t h
  induction t with
  | empty _ => simp at h
  | leaf y _ _ => simp [Stree.exists] at *; exact h
  | node y l r left_ih right_ih =>
    simp at h
    cases h with
    | inl hp =>
      cases hp with
      | inl hpp => apply Exists.intro y; simp [hpp]
      | inr hpq =>
        simp
        obtain ⟨ x, hx ⟩ := left_ih hpq
        apply Exists.intro x
        simp [hx]
    | inr hq =>
      simp
      obtain ⟨ x, hx ⟩ := right_ih hq
      apply Exists.intro x
      simp [hx]

def Stree.coeLow {α : Type} [l : LinearOrder α] : ∀ {low high : Bounded α} {h : low < high} (b : Bounded α) (blow : b < low),
  Stree α h → @Stree α l b high (lt_trans blow h) :=
  fun b blow t =>
    match t with
    | (Stree.empty _) => Stree.empty (lt_trans blow (by assumption))
    | (Stree.leaf x lowx highx)  => Stree.leaf x (lt_trans blow lowx) highx
    | (@Stree.node α l _ _ x q _ left right) => Stree.node x (@Stree.coeLow α l _ (element x) q b blow left) right

def Stree.coeHigh {α : Type} [l : LinearOrder α] : ∀ {low high : Bounded α} {h : low < high} (b : Bounded α) (bhigh : high < b),
  Stree α h → @Stree α l low b (lt_trans h bhigh) :=
  fun b bhigh t =>
    match t with
    | (Stree.empty _) => Stree.empty (lt_trans' bhigh (by assumption))
    | (Stree.leaf x lowx highx)  => Stree.leaf x lowx (lt_trans highx bhigh)
    | (@Stree.node α l _ _ x _ r left right) => Stree.node x left (@Stree.coeHigh α l (element x) _ r b bhigh right)

def Stree.coe {α : Type} [l : LinearOrder α] {low high low' high' : Bounded α} (h : low < high) (h' : low' < high') (eqLow : low' = low) (eqHigh : high' = high) :
  Stree α h → Stree α h'
    | (Stree.empty _) => Stree.empty _
    | (Stree.leaf x lowx highx)  => Stree.leaf x (by { rw [eqLow]; exact lowx }) (by { rw [eqHigh]; exact highx })
    | (Stree.node x left right) => 
      (Stree.node x 
        (Stree.coe (_) (by { rw [eqLow]; assumption }) (eqLow) (by rfl) left)
        (Stree.coe (_) (by { rw [eqHigh]; assumption }) (by rfl) (eqHigh) right)
      )

def Stree.intersection {α : Type} [l : LinearOrder α] :
  ∀ {low high : Bounded α} {b : low < high},
  Stree α b → Stree α b → Stree α b
| _, _, b, (Stree.empty _), t => Stree.empty b
| _, _, b, t, (Stree.empty _) => Stree.empty b
| _, _, b, (Stree.leaf x _ _), (Stree.leaf y _ _) => 
  if x = y then (Stree.leaf x (by assumption) (by assumption)) 
  else Stree.empty b
| _, _, b, (Stree.leaf x _ _), (Stree.node y left right) =>
  if x = y then (Stree.leaf x (by assumption) (by assumption)) 
  else if Stree.elem x left then (Stree.leaf x (by assumption) (by assumption))
  else if Stree.elem x right then (Stree.leaf x (by assumption) (by assumption))
  else Stree.empty b
| _, _, b, (Stree.node x left right), (Stree.leaf y _ _) => 
  if x = y then (Stree.leaf x (by assumption) (by assumption)) 
  else if Stree.elem y left then (Stree.leaf y (by assumption) (by assumption))
  else if Stree.elem y right then (Stree.leaf y (by assumption) (by assumption))
  else Stree.empty b
| low, high, b, (@Stree.node α l _ _ x q r left right), (@Stree.node α l _ _ x' q' r' left' right') =>
  if H : x = x' then (Stree.node x 
    (@intersection α l low (element x) q left (Stree.coe q' q rfl (by rw [H]) left'))
    (@intersection α l (element x) high r right (Stree.coe r' r (by rw [H]) rfl right')))
  else sorry

def Tset (α : Type) [lo : LinearOrder α] := @Stree α lo bottom top (by rfl)

def Tset.mem {α : Type} [LinearOrder α] (x : α) (t : Tset α) := Stree.elem x t

def Tset.option_mem {α : Type} [LinearOrder α] (x : α) : Option (Tset α) → Bool
  | none => false
  | (some t) => Tset.mem x t
  
instance Tset.has_mem {α : Type} [LinearOrder α]: Membership α (Tset α) where
  mem := fun x t => Tset.mem x t
  
instance Tset.option_has_mem {α : Type} [LinearOrder α] : Membership α (Option (Tset α)) where
  mem := fun x t => Tset.option_mem x t

instance Tset.has_insert {α : Type} [LinearOrder α]: Insert α (Tset α) where
  insert := fun x t => Stree.insert x t rfl rfl 

def Tset.add {α : Type} [l : LinearOrder α] (x : α) (t : Tset α) := @Stree.insert α l x bottom top (by rfl) t 

lemma Tset.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
  ∀ (t : Tset α), Stree.forall p t = true → ∀ (x : α), x ∈ t → p x :=
  by apply Stree.forall_is_forall

-- def Tset.intersection {α : Type} [LinearOrder α] : Tset α → Tset α → Tset α := sorry
end TreeSet