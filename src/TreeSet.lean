import BoundedOrder
import OrdEq

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

@[simp, reducible]
instance STree.hasMem {α : Type} [Ord α] : Membership α (STree α) where
  mem := fun x t => t.mem x

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
def STree.all {α : Type} [Ord α] (t : STree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => true
  | leaf x => p x
  | node x left right => p x && left.all p && right.all p

theorem STree.all_forall {α : Type} [Ord α] [OrdEq α] (t : STree α) (p : α → Prop) [DecidablePred p] :
  t.all p → ∀ x, STree.mem x t → p x := by
  induction t
  case empty => simp
  case leaf y =>
    simp
    intros py x
    cases (OrdEq_cases x y) with
    | inl H => simp [H]
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; assumption
      | inr H => simp [H]
  case node y left right ihl ihr =>
    simp
    intros px all_left all_right x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left] ; apply ihl all_left
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; assumption
      | inr H => simp [H.left] ; apply ihr all_right

@[simp]
def STree.exi {α : Type} [Ord α] (t : STree α) (p : α → Prop) [DecidablePred p] : Bool :=
  match t with
  | empty => false
  | leaf x => p x
  | node x left right => p x || left.exi p || right.exi p

theorem STree.exists_exi {α : Type} [Ord α] [OrdEq α] (p : α → Prop) [DecidablePred p] :
  ∀ (t : STree α), (∃ x, STree.mem x t ∧ p x) → t.exi p = true := by
  intro t
  induction t
  case empty => simp
  case leaf y =>
    simp
    intro x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left]
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; intro ; assumption
      | inr H => simp [H.left]
  case node y left right ihl ihr =>
    simp
    intro x
    cases (OrdEq_cases x y) with
    | inl H => simp [H.left] ; intros ; apply Or.inl ; apply Or.inr ; apply ihl ; exists x
    | inr G =>
      cases G with
      | inl H => simp [H.left] ; rw [H.right] ; intro ; apply Or.inl ; apply Or.inl ; assumption
      | inr H => simp [H.left] ; intros ; apply Or.inr ; apply ihr ; exists x

-- The underlying set of the tree
@[reducible, simp]
def STree.set {α : Type} [Ord α] (t : STree α) := { x : α // t.mem x }

def STree.size_is_card {α : Type} [Ord α] [Fintype α] (t : STree α) :
  Fintype.card t.set = t.size := sorry

end HoG
