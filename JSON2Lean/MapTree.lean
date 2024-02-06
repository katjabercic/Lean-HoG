import Lean
import JSON2Lean.BoundedOrder

namespace JSON2Lean

/--
  We implement finite maps as search trees. These need not be balanced (and therefore) may
  be infefficient, but we always construct them as balanced trees, so they are efficient.
-/
inductive MapTree (α β : Type) : Type
| empty : MapTree α β
| leaf : α → β → MapTree α β
| node : α → β → MapTree α β → MapTree α β → MapTree α β
deriving Inhabited

/--
  Given a subarray of key-value pairs, generate the corresponding balanced search tree.
  NB: The subarray must be sorted by keys.
-/
partial def MapTree.ofSubarray {α β : Type} (arr : Array (α × β)) (low high : ℕ) : MapTree α β :=
  if ltSize : low < arr.size ∧ high <= arr.size then
    if _ : low >= high then
      .empty
    else if low + 1 = high then
      let (k, v) := arr[low]'(ltSize.1)
      .leaf k v
    else
      let middle := (low + high).div2
      let left :=  ofSubarray arr low middle
      let right := ofSubarray arr (middle + 1) high
      have middle_valid : (low + high).div2 < arr.size := (by
        rw [Nat.div2_val]
        have h : (low + high < arr.size + arr.size) → ((low + high) / 2 < arr.size) := (by
          intro ab_lt_nn
          rw [←Nat.two_mul] at ab_lt_nn
          apply Nat.div_lt_of_lt_mul ab_lt_nn)
        apply h
        apply Nat.lt_of_le_of_lt (Nat.add_le_add_left ltSize.2 low) (Nat.add_lt_add_right ltSize.1 arr.size))
      let (k, v) := arr[middle]'middle_valid
      .node k v left right
  else
    .empty

/--
  Given an array of key-value pairs, generate the corresponding balanced search tree.
  NB: The array must be sorted by keys.
-/
def MapTree.ofArray {α β : Type} (arr : Array (α × β)) : MapTree α β :=
  ofSubarray arr 0 arr.size

/--
  The definition of a tree does not actually require it to be a search tree.
  This predicate states that a given tree is a search tree with the given
  bounds on the keys contained in it.
-/
def MapTree.correctBound {α β : Type} [Ord α] (low high : Bounded α) : MapTree α β → Bool
  | .empty => true
  | .leaf x _ =>
    match compare low (.element x) with
    | .lt =>
      match compare (.element x) high with
      | .lt => true
      | _ => false
    | _ => false
  | node x _ left right =>
    match compare low x with
    | .lt =>
      match compare (.element x) high with
      | .lt => correctBound low (.element x) left && correctBound (.element x) high right
      | _ => false
    | _ => false

/--
  The given tree is a valid search tree.
-/
def MapTree.correct {α β : Type} [Ord α] (m : MapTree α β) : Bool :=
  correctBound .bottom .top m

/--
  Lookup the value corresponding to the given key, optionally.
-/
def MapTree.get? {α β : Type} [Ord α] (m : MapTree α β) (x : α) : Option β :=
  match m with
  | .empty => none
  | .leaf y vy =>
    match compare x y with
    | .eq => some vy
    | _ => none
  | .node y vy left right =>
    match compare x y with
    | .lt => get? left x
    | .eq => some vy
    | .gt => get? right x

/--
  Lookup the value corresponding to the given key, return a default value
  if none is found.
-/
def MapTree.getD {α β : Type} [Ord α] (m : MapTree α β) (y₀ : β) (x : α) : β :=
  match m with
  | .empty => y₀
  | .leaf y vy =>
    match compare x y with
    | .eq => vy
    | _ => y₀
  | .node y vy left right =>
    match compare x y with
    | .lt => getD left y₀ x
    | .eq => vy
    | .gt => getD right y₀ x

/--
  A relation stating that the given key maps to the given value.
-/
def MapTree.mapsTo {α β} [Ord α] (m : MapTree α β) (x : α) (y : β) : Prop :=
  match m.get? x with
  | none => false
  | some z => y = z

/--
  Does the map contain a given key?
-/
def MapTree.hasKey {α β : Type} [Ord α] (x : α) : MapTree α β → Bool
  | .empty => false
  | .leaf y _ =>
    match compare x y with
    | .eq => true
    | _ => false
  | .node y _ left right =>
    match compare x y with
    | .lt => hasKey x left
    | .eq => true
    | .gt => hasKey y right

end JSON2Lean
