import BoundedOrder

import TreeSet

-- Type of finite maps
inductive Map (α β : Type) : Type
| empty : Map α β
| leaf : α → β → Map α β
| node : α → β → Map α β → Map α β → Map α β

-- Get the domain of a finite map as a Tree
def Map.domain {α β : Type} [Ord α] : Map α β → Tree α
  | empty => Tree.empty
  | leaf x _ => Tree.leaf x
  | node x _ left right => Tree.node x (left.domain) (right.domain)

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

def Map.mapsTo {α β} [Ord α] (m : Map α β) (x :α) (y : β) : Prop :=
  match m.get x with
  | none => false
  | some z => y = z

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

def Map.hasVal {α β : Type} [Ord α] [DecidableEq β] (x : β) : Map α β → Bool
  | empty => false
  | leaf _ y => x == y
  | node _ y left right => x == y || left.hasVal x || right.hasVal x

def Map.forallKeys {α β : Type} [Ord α] (p : α → Prop) [DecidablePred p] : Map α β → Bool
  | empty => true
  | leaf x _ => p x
  | node x _ left right =>
    p x && left.forallKeys p && right.forallKeys p

def Map.forall {α β : Type} [Ord α] (p : β → Prop) [DecidablePred p] : Map α β → Bool
  | empty => true
  | leaf _ y => p y
  | node _ y left right =>
    p y && left.forall p && right.forall p

theorem Map.all_forall {α β: Type} [Ord α] [DecidableEq β] (p : β → Prop) [DecidablePred p] (m : Map α β) : 
  Map.forall p m → (∀ x : β, Map.hasVal x m → p x) := by
  induction m
  case empty => simp [Map.hasVal]
  case leaf _ x =>
    intros ih x' ih'
    simp [Map.forall] at ih
    simp [Map.hasVal] at ih'
    rw [ih']
    assumption
  case node a y left right ihl ihr =>
    intros h x ih
    simp [Map.forall] at h
    simp [Map.hasVal] at ih
    cases ih with
    | inl l =>
      cases l with
      | inl ll => simp [h, ll]
      | inr lr => simp [h, ihl, lr]
    | inr r => simp [ihr, h, r]
      
def Map.exi {α β : Type} [Ord α] (p : β → Prop) [DecidablePred p] : Map α β → Bool
  | empty => false
  | leaf _ x => p x
  | node _ x left right => p x || left.exi p || right.exi p

theorem Map.exists_exi {α β: Type} [Ord α] [DecidableEq β] (p : β → Prop) [DecidablePred p] (m : Map α β) : 
  (∃ (x : β), Map.hasVal x m → p x) → Map.exi p m := sorry


