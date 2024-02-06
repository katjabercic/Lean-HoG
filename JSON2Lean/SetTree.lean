import Mathlib

import JSON2Lean.BoundedOrder

namespace JSON2Lean

/--  A finite set represented as a search tree. --/
inductive SetTree.{u} (α : Type u) : Type u
  | empty : SetTree α
  | leaf : α → SetTree α
  | node : α → SetTree α → SetTree α → SetTree α
deriving Repr, Inhabited

/--
  The given tree is a valid search tree with elements within given bounds.
-/
def SetTree.correctBound {α : Type} [Ord α] (low high : Bounded α) : SetTree α → Bool
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

/--
  The given tree is a valid search tree.
-/
def SetTree.isCorrect {α : Type} [Ord α] (t : SetTree α) : Bool :=
  correctBound .bottom .top t

/-- The given element appears in the tree. -/
@[simp]
def SetTree.mem {α : Type} [Ord α] (x : α) : SetTree α → Bool
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

/-- The membership predicate for the set represented by a tree. -/
instance SetTree.hasMem {α : Type} [Ord α] : Membership α (SetTree α) where
  mem := fun x t => t.mem x

/-- The number of elements in the tree within the given bounds. -/
def SetTree.sizeBounded {α : Type} [Ord α] (low high : Bounded α) : SetTree α → Nat
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

/-- The number of elements in a tree. -/
@[simp]
def SetTree.size {α : Type} [Ord α] (t : SetTree α) : Nat :=
  sizeBounded .bottom .top t

/-- Universal quantification over the elements of a tree. -/
@[simp]
def SetTree.all {α : Type} [Ord α] (t : SetTree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => true
  | leaf x => p x
  | node x left right => p x && left.all p && right.all p

/-- If a statement holds for all vertices in the tree, then it holds for all
    elements of the set represented by the tree. Note taht since we do not assume
    the tree to be correct, there may be some vertices that are not finable by
    binary search, and these do not appear in the represented set. -/
theorem SetTree.all_forall {α : Type} [LinearOrder α] (t : SetTree α) (p : α → Prop) [DecidablePred p] :
  t.all p → ∀ x, SetTree.mem x t → p x := by
  induction t
  case empty => simp
  case leaf y =>
    simp
    intros py x
    cases (lt_trichotomy x y) with
    | inl x_lt_y => simp [compare_lt_iff_lt.mpr x_lt_y]
    | inr G =>  
      cases G with
      | inl x_eq_y => simp [compare_eq_iff_eq.mpr x_eq_y] ; rw [x_eq_y] ; assumption
      | inr y_lt_x => simp [compare_gt_iff_gt.mpr (gt_iff_lt.mpr y_lt_x)]
  case node y left right ihl ihr =>
    simp
    intros px all_left all_right x
    cases (lt_trichotomy x y) with
    | inl x_lt_y => simp [compare_lt_iff_lt.mpr x_lt_y] ; apply ihl all_left
    | inr G =>
      cases G with
      | inl x_eq_y => simp [compare_eq_iff_eq.mpr x_eq_y] ; rw [x_eq_y] ; assumption
      | inr y_lt_x => simp [compare_gt_iff_gt.mpr (gt_iff_lt.mpr y_lt_x)] ; apply ihr all_right

/-- Does there exists an element in the tree that satisfies the given property? -/
@[simp]
def SetTree.exi {α : Type} [Ord α] (t : SetTree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => false
  | leaf x => p x
  | node x left right => p x || left.exi p || right.exi p

/--
  If the finite set represented by the tree has an element satisfying a given property,
  then the tree contains an element satisfying the property. Note that the converse
  need not hold because we are not assumnig that the tree is correct. -/
theorem SetTree.exists_exi {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : SetTree α), (∃ x, SetTree.mem x t ∧ p x) → t.exi p = true := by
  intro t
  induction t
  case empty => simp
  case leaf y =>
    simp
    intro x
    cases (lt_trichotomy x y) with
    | inl x_lt_y => simp [compare_lt_iff_lt.mpr x_lt_y]
    | inr G =>
      cases G with
      | inl x_eq_y => simp [compare_eq_iff_eq.mpr x_eq_y] ; rw [x_eq_y] ; intro ; assumption
      | inr y_lt_x => simp [compare_gt_iff_gt.mpr (gt_iff_lt.mpr y_lt_x)]
  case node y left right ihl ihr =>
    simp
    intro x
    cases (lt_trichotomy x y) with
    | inl x_lt_y => simp [compare_lt_iff_lt.mpr x_lt_y] ; intros ; apply Or.inl ; apply Or.inr ; apply ihl ; exists x
    | inr G =>
      cases G with
      | inl x_eq_y => simp [compare_eq_iff_eq.mpr x_eq_y] ; rw [x_eq_y] ; intro ; apply Or.inl ; apply Or.inl ; assumption
      | inr y_lt_x => simp [compare_gt_iff_gt.mpr (gt_iff_lt.mpr y_lt_x)] ; intros ; apply Or.inr ; apply ihr ; exists x

/-- The underlying set of the tree -/
@[reducible]
def SetTree.set {α : Type} [Ord α] (t : SetTree α) := { x : α // t.mem x }

end JSON2Lean
