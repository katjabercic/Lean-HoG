import BoundedOrder
import OrdEq

namespace HoG

inductive Map (α β : Type) : Type
| empty : Map α β
| leaf : α → β → Map α β
| node : α → β → Map α β → Map α β → Map α β

@[simp]
def Map.correctBound {α β : Type} [Ord α] (low high : Bounded α) : Map α β → Bool
  | empty => true
  | leaf x _ =>
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

@[simp]
def Map.correct {α β : Type} [Ord α] (m : Map α β) : Bool :=
  correctBound .bottom .top m

def Map.get? {α β : Type} [Ord α] (m : Map α β) (x : α) : Option β :=
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

def Map.getD {α β : Type} [Ord α] (m : Map α β) (y₀ : β) (x : α) : β :=
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

def Map.mapsTo {α β} [Ord α] (m : Map α β) (x : α) (y : β) : Prop :=
  match m.get? x with
  | none => false
  | some z => y = z

def Map.hasKey {α β : Type} [Ord α] (x : α) : Map α β → Bool
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

end HoG
