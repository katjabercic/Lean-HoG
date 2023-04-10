inductive Map (α β : Type) : Type
| empty : Map α β
| leaf : α → β → Map α β
| node : α → β → Map α β → Map α β → Map α β

def Map.get {α β : Type} [Ord α] (m : Map α β) (x : α) : Option β :=
  match m with
  | .empty => none
  | .leaf y vy =>
    match compare x y with
    | .eq => some vy
    | _ => none
  | .node y vy left right =>
    match compare x y with
    | .lt => get left x
    | .eq => some vy
    | .gt => get right x

def Map.hasKey {α β : Type} [Ord α] (x : α) : Map α β → Bool
  | empty => false
  | leaf y _ =>
    match compare x y with
    | .eq => true
    | _ => false
  | node y _ left right =>
    match compare x y with
    | .lt => hasKey x left
    | .eq => true
    | .gt => hasKey y right
