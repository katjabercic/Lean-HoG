import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.Basic

import BoundedOrder

namespace HoG

-- A finite set represented as a search tree
-- (There is already Mathlib.Data.Tree that defines Tree, so we use STree for "set tree")
inductive STree .{u} (α : Type u) : Type u
  | empty : STree α
  | leaf : α → STree α
  | node : α → STree α → STree α → STree α

open STree

@[simp]
def STree.correctBound {α : Type} [Ord α] (low high : Bounded α) : STree α → Bool
  | empty => true
  | leaf x =>
    match compare low (.element x) with
    | .lt =>
      match compare (.element x) high with
      | .lt => true
      | _ => false
    | _ => false
  | node x left right =>
    match compare low x with
    | .lt =>
      match compare (.element x) high with
      | .lt => correctBound low (.element x) left && correctBound (.element x) high right
      | _ => false
    | _ => false

-- The tree is a search tree
@[simp]
def STree.correct {α : Type} [Ord α] (t : STree α) : Bool :=
  correctBound .bottom .top t

@[simp]
def STree.mem {α : Type} [Ord α] (x : α) : STree α → Bool
  | empty => false
  | leaf y =>
    match compare x y with
    | .eq => true
    | _ => false
  | node y left right =>
    match compare x y with
    | .lt => mem x left
    | .eq => true
    | .gt => mem x right

@[simp]
instance hasMem {α : Type} [Ord α] : Membership α (STree α) where
  mem := (fun x t => ↑ (STree.mem x t))

@[simp]
def STree.sizeBounded {α : Type} [Ord α] (low high : Bounded α) : STree α → Nat
  | empty => 0
  | leaf x  =>
    match compare low (.element x) with
    | .lt =>
      match compare (.element x) high with
      | .lt => 1
      | _ => 0
    | _ => 0
  | node x left right =>
    1 + sizeBounded low x left + sizeBounded x high right

@[simp]
def STree.size {α : Type} [Ord α] (t : STree α) : Nat :=
  sizeBounded .bottom .top t

@[simp]
def all {α : Type} [Ord α] (p : α → Prop) [DecidablePred p] : STree α → Bool
  | empty => true
  | leaf x => p x
  | node x left right => p x && all p left && all p right

theorem all_forall {α : Type} [l : LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : STree α), all p t → ∀ x, STree.mem x t → p x := by
  intro t
  induction t
  case empty => simp
  case leaf y =>
    simp
    intros py x
    simp [l.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    apply lt_by_cases x y
    · intro x_lt_y ; simp [x_lt_y]
    · intro x_eq_y ; simp [x_eq_y] ; assumption
    · intro y_lt_x
      simp [not_lt_of_gt y_lt_x, ne_iff_lt_or_gt.mpr (Or.inr y_lt_x)]
  case node y left right ihl ihr =>
    simp
    intros px all_left all_right x
    simp [l.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    apply lt_by_cases x y
    · intros x_lt_y
      simp [x_lt_y]
      apply ihl ; assumption
    · intros x_eq_y
      simp [x_eq_y]
      intros
      exact px
    · intros y_lt_x
      simp [not_lt_of_gt y_lt_x, ne_iff_lt_or_gt.mpr (Or.inr y_lt_x)]
      intro
      apply ihr <;> assumption

@[simp]
def exi {α : Type} [Ord α] (p : α → Prop) [DecidablePred p] : STree α → Bool
  | empty => false
  | leaf x => p x
  | node x left right => p x || exi p left || exi p right

theorem exists_exi {α : Type} [l : LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : STree α), (∃ x, STree.mem x t ∧ p x) → exi p t := by
  intro t
  induction t
  case empty => intro q ; simp at q
  case leaf y =>
    simp
    simp [l.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    intro x
    apply lt_by_cases x y
    · intro x_lt_y ; simp [x_lt_y]
    · intro x_eq_y ; simp [x_eq_y]
    · intro y_lt_x
      simp [not_lt_of_gt y_lt_x, ne_iff_lt_or_gt.mpr (Or.inr y_lt_x)]
  case node y left right ihl ihr =>
    simp [l.compare_eq_compareOfLessAndEq, compareOfLessAndEq]
    intros x q px
    apply lt_by_cases x y
    ·  intros x_lt_y
       simp [x_lt_y] at q
       apply Or.inl
       apply Or.inr
       apply ihl
       exists x
    · intros x_eq_y
      apply Or.inl
      apply Or.inl
      rw [x_eq_y] at px
      assumption
    · intros y_lt_x
      have x_neq_y : x ≠ y := ne_iff_lt_or_gt.mpr (Or.inr y_lt_x)
      simp [not_lt_of_gt y_lt_x, x_neq_y] at q
      apply Or.inr
      apply ihr
      exists x

end HoG