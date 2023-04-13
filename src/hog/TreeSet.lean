import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.Basic

import BoundedOrder

-- A finite set represented as a search tree

inductive Tree (α : Type) : Type
  | empty : Tree α
  | leaf : α → Tree α
  | node : α → Tree α → Tree α → Tree α

open Tree

@[simp]
def Tree.correctBound {α : Type} [Ord α] (low high : Bounded α) : Tree α → Bool
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

@[simp]
def Tree.correct {α : Type} [Ord α] (t : Tree α) : Bool :=
  correctBound .bottom .top t

@[simp]
def Tree.mem {α : Type} [Ord α] (x : α) : Tree α → Bool
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
instance hasMem {α : Type} [Ord α] : Membership α (Tree α) where
  mem := (fun x t => ↑ (Tree.mem x t))

@[simp]
def Tree.sizeBounded {α : Type} [Ord α] (low high : Bounded α) : Tree α → Nat
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
def Tree.size {α : Type} [Ord α] (t : Tree α) : Nat :=
  sizeBounded .bottom .top t

@[simp]
def all {α : Type} [Ord α] (p : α → Prop) [DecidablePred p] : Tree α → Bool
  | empty => true
  | leaf x => p x
  | node x left right => p x && all p left && all p right

theorem all_forall {α : Type} [l : LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : Tree α), all p t → ∀ x, Tree.mem x t → p x := by
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
def exi {α : Type} [Ord α] (p : α → Prop) [DecidablePred p] : Tree α → Bool
  | empty => false
  | leaf x => p x
  | node x left right => p x || exi p left || exi p right

theorem exists_exi {α : Type} [l : LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : Tree α), (∃ x, Tree.mem x t ∧ p x) → exi p t := by
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
