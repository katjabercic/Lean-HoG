/-
Auxiilary functions and theorems to build the Std red-black trees and sets from a sorted array in linear time.
-/
import Std.Data.RBMap
import Mathlib.Init.Data.Nat.Bitwise
import Mathlib.Data.Nat.Order.Basic
import Qq
open Qq
open Std.RBNode

/-
A red-black tree requires every path to a nil to contain the same number of black vertices. The nil nodes are usually considered black.
With the way we build those, the length of two paths from a node to a leaf can only difer by at most 1.
So we only need to set the deepest, non nil nodes to be red. We are given this maximum depth as targeted_depth.
-/
partial def _build_RBNode {α : Q(Type)} (arr : Array Q($α)) (targeted_depth depth low high : Nat) : Q(Std.RBNode $α) :=
  if ltSize : low < arr.size ∧ high <= arr.size then
    if _ : low >= high then
      q(.nil)
    else if low + 1 = high then
      let x := arr[low]'(ltSize.1)
      -- since we want the deepest nodes to be red, it can only happen if they are leaves
      if depth == targeted_depth then
        q(.node .red nil $x nil)
      else
        q(.node .black nil $x nil)
    else
      let middle := (low + high).div2
      let left :=  _build_RBNode arr targeted_depth (depth + 1) low middle
      let right := _build_RBNode arr targeted_depth (depth + 1) (middle + 1) high
      have middle_valid : (low + high).div2 < arr.size := (by
        rw [Nat.div2_val]
        have h : (low + high < arr.size + arr.size) → ((low + high) / 2 < arr.size) := (by
          intro ab_lt_nn
          rw [←Nat.two_mul] at ab_lt_nn
          apply Nat.div_lt_of_lt_mul ab_lt_nn)
        apply h
        apply Nat.lt_of_le_of_lt (Nat.add_le_add_left ltSize.2 low) (Nat.add_lt_add_right ltSize.1 arr.size))
      let x := arr[middle]'middle_valid
      q(.node .black $left $x $right)
  else
    q(.nil)

/-
Given a number of values, computes the maximum depth of a node in a balanced binary tree. The formula is ceil(log2(n+1))-1. Note, we start counting the depth from zero.
-/
def max_depth (n : Nat) : Nat :=
  let log := Nat.log2 (n+1)
  -- I could not find a ceil function for log2 so we simply ignore the -1 if we are too low
  if Nat.pow 2 log < (n+1) then
    log
  else
    log - 1

/--
  Given an array of values, generate the corresponding red black tree. The depth is the maximum depth of the tree, starting from zero and not counting the nil nodes. It can be obtained using the max_depth function.
  NB: The array must be sorted by keys.
-/
def build_RBNode {α : Q(Type)} (depth : Nat) (arr : Array Q($α)) : Q(Std.RBNode $α) :=
  _build_RBNode arr depth 0 0 arr.size

/-
Verifies if a tree is balanced (in the red black tree definition). We need the height of the tree (starting from zero and not counting nil nodes) and a boolean to know if the node must be black (a red node can only have black children).
-/
def is_balanced {α : Type} (height : Nat) (must_be_black : Bool) : Std.RBNode α → Bool
| .nil =>
  if height = 0 then
    true
  else
    false
| .node color left _ right =>
  match color with
  | .black =>
    0 < height
    && is_balanced (Nat.pred height) false left
    && is_balanced (Nat.pred height) false right
  | .red =>
    if must_be_black then
      false
    else
      is_balanced height true left
      && is_balanced height true right

/-
Shows that if is_balanced returns true, then the color of the node enforced by must_be_black is respected. We use isRed because it gives nil nodes a black color (isRed returns the color despite its name)
-/
theorem must_be_black_respected {α : Type} (n : Std.RBNode α) (height : Nat) : is_balanced height true n = true → isRed n = .black := by
  induction n with
  | nil =>
    intro
    unfold isRed
    simp
  | node col =>
    induction col with
    | red =>
      unfold is_balanced
      simp
    | black =>
      unfold is_balanced
      simp
      intros
      unfold isRed
      simp


/-
Shows that if is_balanced returns true, the tree has the Balanced property (isRed returns the color despite its name).
-/
theorem is_balanced_impl_balanced {α : Type} (n : Std.RBNode α) :
  (color : Std.RBColor) →
  color = (isRed n) →
  (must_be_black : Bool) →
  (height : Nat) →
  is_balanced height must_be_black n = true →
  Std.RBNode.Balanced n color height
:= by
  induction n with
  | nil =>
    intro color
    unfold isRed
    simp
    intro right_color
    subst right_color
    unfold is_balanced
    simp
    exact Std.RBNode.Balanced.nil
  | node col left _ right left_balanced right_balanced =>
    let left_col := isRed left
    have left_col_ok : left_col = isRed left := by rfl
    specialize left_balanced left_col left_col_ok
    let right_col := isRed right
    have right_col_ok : right_col = isRed right := by rfl
    specialize right_balanced right_col right_col_ok
    induction col with
    | black =>
      unfold is_balanced
      simp
      unfold isRed
      simp
      intro height
      intro pos_height is_balanced_left_true is_balanced_right_true
      apply left_balanced at is_balanced_left_true
      apply right_balanced at is_balanced_right_true
      have pred_height_plus_one : height = Nat.pred height + 1 := by
        rw [← Nat.succ_eq_add_one, Nat.succ_pred]
        apply Nat.ne_of_gt pos_height
      rw [pred_height_plus_one]
      exact Std.RBNode.Balanced.black is_balanced_left_true is_balanced_right_true
    | red =>
      unfold is_balanced
      simp
      unfold isRed
      simp
      intro height
      intro is_balanced_left_true is_balanced_right_true
      have left_is_black : isRed left = .black := by
        apply must_be_black_respected
        assumption
      have right_is_black : isRed right = .black := by
        apply must_be_black_respected
        assumption
      apply left_balanced at is_balanced_left_true
      apply right_balanced at is_balanced_right_true
      rw [left_col_ok, left_is_black] at is_balanced_left_true
      rw [right_col_ok, right_is_black] at is_balanced_right_true
      exact Std.RBNode.Balanced.red is_balanced_left_true is_balanced_right_true

/-
Utility theorem to show that the tree has the WF property if it has the Ordered and the Balanced properties.
-/
theorem is_wf {α : Type} (node : Std.RBNode α) (col : Std.RBColor) (cmp : α → α → Ordering) (height : Nat) (ord : Std.RBNode.Ordered cmp node) (bal : Std.RBNode.Balanced node col height) : Std.RBNode.WF cmp node := by
  exact Std.RBNode.WF.mk ord bal

/-
Utility function that checks that a node has the right color.
-/
def check_color {α : Type} (n : Std.RBNode α) (color : Std.RBColor) : Bool :=
  match n, color with
  | .nil, .black => true
  | .nil, .red => false
  | .node .black _ _ _, .black => true
  | .node .red _ _ _, .red => true
  | _, _ => false

/-
Shows that using check_color is equivalent to using isRed.
-/
theorem check_color_iff {α : Type} (n : Std.RBNode α) (color : Std.RBColor) : check_color n color = true ↔ color = isRed n := by
  unfold check_color
  unfold isRed
  induction n with
  | nil =>
    induction color with
    | black => simp
    | red => simp
  | node n_color _ _ _ =>
    induction n_color with
    | black =>
      induction color with
      | black => simp
      | red => simp
    | red =>
      induction color with
      | black => simp
      | red => simp

/-
Simplifies the code by making the color of a node decidable.
-/
instance decideColor {α : Type} (n : Std.RBNode α) (color : Std.RBColor) : Decidable (color = isRed n) :=
  decidable_of_iff (check_color n color = true) (check_color_iff n color)

/-
Builds an RBSet from an array and a LinearOrder in the data type.
LinearOrder is required to have a decidable Ordered property
-/
def build_RBSet {α : Q(Type)} (arr : Array Q($α)) (linOrder : Q(LinearOrder $α)) : Q(Std.RBSet $α $(linOrder).compare) :=
  let h : Nat := max_depth arr.size
  have nodeQ : Q(Std.RBNode $α) := build_RBNode h arr
  have color : Q(Std.RBColor) := if h = 0 && arr.size > 0 then q(.red) else q(.black)
  have height : Q(Nat) := q($h)
  have decideIsOrdered : Q(decide (Std.RBNode.Ordered $(linOrder).compare $nodeQ) = true) := (q(Eq.refl true) : Lean.Expr)
  have isOrdered : Q(Std.RBNode.Ordered $(linOrder).compare $nodeQ) := (q(of_decide_eq_true $decideIsOrdered))
  have decideIsCorrectColor : Q(decide ($color = isRed $nodeQ) = true) := (q(Eq.refl true) : Lean.Expr)
  have isCorrectColor : Q($color = isRed $nodeQ) := (q(of_decide_eq_true $decideIsCorrectColor) : Lean.Expr)
  have isBalancedAlgo : Q(is_balanced $height false $nodeQ = true) := (q(Eq.refl true) : Lean.Expr)
  have isBalanced : Q(Std.RBNode.Balanced $nodeQ $color $height) := (q(is_balanced_impl_balanced $nodeQ $color $isCorrectColor false $height $isBalancedAlgo) : Lean.Expr)
  have isWF : Q(Std.RBNode.WF $(linOrder).compare $nodeQ) := (q(is_wf $nodeQ $color $(linOrder).compare $height $isOrdered $isBalanced) : Lean.Expr)
  have treeQ : Q(Std.RBSet $α $(linOrder).compare) := (q(⟨$nodeQ, $isWF⟩))
  treeQ

/-
Builds an RBMap from an array and a LinearOrder in the data type.
LinearOrder is required to have a decidable Ordered property
-/
def build_RBMap {α β : Q(Type)} (arr : Array Q($α × $β)) (linOrder : Q(LinearOrder $α)) : Q(Std.RBMap $α $β $(linOrder).compare) :=
  let h : Nat := max_depth arr.size
  have nodeQ : Q(Std.RBNode ($α × $β)) := build_RBNode h arr
  have color : Q(Std.RBColor) := if h = 0 && arr.size > 0 then q(.red) else q(.black)
  have height : Q(Nat) := q($h)
  have decideIsOrdered : Q(decide (Std.RBNode.Ordered (Ordering.byKey Prod.fst ($linOrder).compare) $nodeQ) = true) := (q(Eq.refl true) : Lean.Expr)
  have isOrdered : Q(Std.RBNode.Ordered (Ordering.byKey Prod.fst ($linOrder).compare) $nodeQ) := (q(of_decide_eq_true $decideIsOrdered))
  have decideIsCorrectColor : Q(decide ($color = isRed $nodeQ) = true) := (q(Eq.refl true) : Lean.Expr)
  have isCorrectColor : Q($color = isRed $nodeQ) := (q(of_decide_eq_true $decideIsCorrectColor) : Lean.Expr)
  have isBalancedAlgo : Q(is_balanced $height false $nodeQ = true) := (q(Eq.refl true) : Lean.Expr)
  have isBalanced : Q(Std.RBNode.Balanced $nodeQ $color $height) := (q(is_balanced_impl_balanced $nodeQ $color $isCorrectColor false $height $isBalancedAlgo) : Lean.Expr)
  have isWF : Q(Std.RBNode.WF (Ordering.byKey Prod.fst ($linOrder).compare) $nodeQ) := (q(is_wf $nodeQ $color (Ordering.byKey Prod.fst ($linOrder).compare) $height $isOrdered $isBalanced) : Lean.Expr)
  have treeQ : Q(Std.RBSet ($α × $β) (Ordering.byKey Prod.fst ($linOrder).compare)) := (q(⟨$nodeQ, $isWF⟩))
  have mapQ : Q(Std.RBMap $α $β ($linOrder).compare) := treeQ
  mapQ
