import Mathlib

-- An order extended with a bottom and a top element at the same time.
-- This is like simultaneous WithBot and MathLib.Order.

namespace JSON2Lean

inductive Bounded (α : Type) : Type
  | bottom : Bounded α
  | element : α -> Bounded α
  | top : Bounded α

open Bounded

instance Bounded_Coe (α : Type) : Coe α (Bounded α) where
  coe x := .element x

@[simp]
def Bounded.compare {α : Type} [α_ord : Ord α] : Bounded α → Bounded α → Ordering :=
  fun x y =>
      match x with
      | bottom =>
        match y with
        | bottom => Ordering.eq
        | _ => Ordering.lt
      | element a =>
        match y with
        | bottom => Ordering.gt
        | element b => α_ord.compare a b
        | top => Ordering.lt
      | top =>
        match y with
        | top => Ordering.eq
        | _ => Ordering.gt

@[simp]
instance Bounded_Ord (α : Type) [Ord α] : Ord (Bounded α) where
  compare := Bounded.compare

@[simp, reducible]
def Bounded.le {α : Type} [LE α] : Bounded α → Bounded α → Prop :=
  fun x y =>
    match x with
    | bottom => true
    | element a =>
      match y with
      | bottom => false
      | element b => a ≤ b
      | top => true
    | top =>
      match y with
      | top => true
      | _ => false

@[simp, reducible]
instance Bounded_LE (α : Type) [LE α] : LE (Bounded α) where
  le := Bounded.le

@[simp]
def Bounded.lt {α : Type} [LT α] : Bounded α → Bounded α → Prop :=
  fun x y =>
    match x with
    | bottom =>
      match y with
      | bottom => false
      | _ => true
    | element a =>
      match y with
      | bottom => false
      | element b => a < b
      | top => true
    | top => false

@[simp]
instance Bounded_LT (α : Type) [LT α] : LT (Bounded α) where
  lt := Bounded.lt

theorem Bounded.le_trans {α : Type} [Preorder α] {a b c : Bounded α} :
  a ≤ b → b ≤ c → a ≤ c := by
  intros a_le_b b_le_c
  cases a <;> cases b <;> cases c <;> try trivial
  · exact (Preorder.le_trans _ _ _ a_le_b b_le_c)

@[simp]
def Bounded.max {α : Type} [m : Max α] : Bounded α → Bounded α → Bounded α :=
  fun x y =>
      match x with
      | bottom => y
      | element a =>
        match y with
        | bottom => element a
        | element b => element (m.max a b)
        | top => top
      | top => top

@[simp]
instance Bounded_Max (α : Type) [Max α] : Max (Bounded α) where
  max := Bounded.max

@[simp]
instance Bounded_Min (α : Type) [Min α] : Min (Bounded α) where
  min := fun x y =>
    match x with
    | bottom => bottom
    | element a =>
      match y with
      | bottom => bottom
      | element b => element (min a b)
      | top => element a
    | top => y

@[simp]
instance Bounded_Preorder (α : Type) [Preorder α] : Preorder (Bounded α) where
  lt := Bounded.lt
  le := Bounded.le
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intros a b c; apply Bounded.le_trans
  lt_iff_le_not_le := by
    intros a b; cases a <;> repeat (first | cases b | tauto | apply lt_iff_le_not_le)

instance Bounded_PartialOrder (α : Type) [PartialOrder α]: PartialOrder (Bounded α) where
  le_antisymm := by
    intros a b h h'
    cases a <;> repeat (first | cases b | rfl | contradiction | simp; apply le_antisymm <;> assumption)

@[simp]
instance Bounded_LinearOrder (α : Type) [la : LinearOrder α] [de : DecidableEq α] : LinearOrder (Bounded α) where

  le_total := by
    intros a b
    cases a <;> cases b <;> simp [LE.le] ; first | apply isTrue True.intro | apply isFalse id | skip
    · apply la.le_total

  decidableLE := by
    intros a b
    cases a <;> cases b <;> simp [LE.le] <;> first | apply isTrue True.intro | apply isFalse id | skip
    · apply la.decidableLE

  decidableEq := by
    intros a b
    cases a <;> cases b <;> simp <;> first | apply isTrue True.intro | apply isFalse id | skip
    · apply de

  decidableLT := by
    intros a b
    cases a <;> cases b <;> simp [LT.lt] <;> first | apply isTrue True.intro | apply isFalse id | skip
    · apply la.decidableLT

  max_def := by
    intros a b
    cases a <;> cases b <;> simp [LT.lt, LE.le]
    · rw [la.max_def]
      apply apply_ite

  min_def := by
    intros a b
    cases a <;> cases b <;> simp [LT.lt, LE.le]
    · rw [la.min_def]
      apply apply_ite

  compare_eq_compareOfLessAndEq := by
    intros a b
    cases a <;> cases b <;> simp [compareOfLessAndEq, LT.lt, la.compare_eq_compareOfLessAndEq]
    case element.element x y => congr


def Bounded.extendFunction {α β : Type} : (α → β) → (α → Bounded β) :=
  fun f x => Bounded.element (f x)

def Bounded.liftFunction {α β : Type} : (α → β) → (Bounded α → Bounded β) :=
  fun f x =>
    match x with
    | bottom => bottom
    | element y => Bounded.extendFunction f y
    | top => top

end JSON2Lean
