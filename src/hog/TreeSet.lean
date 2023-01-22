import Mathlib.Init.Algebra.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Tauto
import Mathlib.Mathport.Syntax
import Init.Core
import Init.Prelude

namespace TreeSet

inductive Bounded (α : Type) : Type
  | bottom : Bounded α 
  | element : α -> Bounded α 
  | top : Bounded α 

open Bounded

instance BoundedHasCoe (α : Type) : Coe α (Bounded α) where
  coe x := .element x

@[simp, reducible]
def Bounded_le {α : Type} [LE α] : Bounded α → Bounded α → Prop
  | bottom, _ => true
  | (element _), bottom => false
  | (element x), (element y) => (x ≤ y)
  | (element _), top => true
  | top, bottom => false
  | top, (element _) => false
  | top, top => true
  
instance Bounded_has_le (α : Type) [LE α] : LE (Bounded α) where
  le := Bounded_le

@[simp, reducible]
def Bounded_lt {α : Type} [LT α] : Bounded α → Bounded α → Prop
  | bottom, bottom => false
  | bottom, (element _) => true
  | bottom, top => true
  | (element _), bottom => false
  | (element x), (element y) => (x < y)
  | (element _), top => true
  | top, _ => false

instance Bounded_has_lt (α : Type) [LT α] : LT (Bounded α) where
  lt := Bounded_lt

theorem Bounded_le_trans {α : Type} [Preorder α] {a b c : Bounded α} :
  Bounded_le a b → Bounded_le b c → Bounded_le a c := by
  intros a_le_b b_le_c
  match a, b with
  | bottom, _ => trivial
  | element x, bottom => contradiction
  | element x, element y => {
    match c with
    | bottom => contradiction
    | element z =>
      simp at a_le_b
      simp at b_le_c
      have h : x ≤ z := by apply le_trans a_le_b b_le_c
      simp [h]
    | top => rfl
  }
  | element x, top => 
    match c with
    | bottom => contradiction
    | element y => contradiction
    | top => rfl
  | top, top =>
    match c with
    | bottom => contradiction
    | element y => contradiction
    | top => rfl

  -- cases_matching* (Bounded α) ; try { tautology },
  -- apply le_trans

instance Bounded_preorder (α : Type) [Preorder α] : Preorder (Bounded α) where
  lt := Bounded_lt
  le_refl := by intro a; cases a <;> trivial
  le_trans := by intros a b c; apply Bounded_le_trans
  lt_iff_le_not_le := by 
    intros a b; cases a <;> repeat (first | cases b | tauto | apply lt_iff_le_not_le)

instance Bounded_partial_order (α : Type) [PartialOrder α]: PartialOrder (Bounded α) where
  le_antisymm := by
    intros a b h h'
    cases a <;> repeat (first | cases b | rfl | contradiction)
    { sorry }
    { contradiction }
    -- match a, b with
    -- | bottom, bottom => rfl
    -- | bottom, element y => contradiction
    -- | bottom, top => contradiction
    -- | element x, bottom => contradiction
    -- | element x, element y => 
    --   have x_eq_y : x = y := by apply le_antisymm <;> tauto
    --   rw [x_eq_y]
    -- | element x, top => contradiction
    -- | top, bottom => contradiction
    -- | top, element y => contradiction
    -- | top, top => rfl

#check instDecidableTrue

example : Decidable True := by
  library_search
  
instance Bounded_linear_order (α : Type) [LinearOrder α] : LinearOrder (Bounded α) where
  le_total := by
    intros a b
    cases a <;> cases b <;> tauto
    apply le_total
  decidable_le := by
    sorry
    -- intros a b
    -- cases a <;> cases b
    -- simp
    -- apply instDecidableTrue
    -- simp
      

inductive Stree (α : Type) [LinearOrder α] : ∀ {low high : Bounded α}, low < high → Type
  | empty : ∀ {low high} (p : low < high), Stree α p
  | leaf : ∀ {low high} (x : α) (lowx : low < element x) (xhigh : element x < high), Stree α (lt_trans lowx xhigh)
  | node : ∀ {low high} (x : α) {q : low < element x} {r : element x < high}
             (left : Stree α q) (right : Stree α r), Stree α (lt_trans q r)


-- example: Stree Nat (by library_search) :=
--   Stree.node 20 
--     (Stree.empty (by library_search))
--     (Stree.leaf 42 (by { sorry } : 20 < 42) (by library_search))

@[reducible]
def Stree.elem {α : Type} [LinearOrder α] (x : α) :
    ∀ {low high : Bounded α} {p : low < high}, Stree α p → Bool
  | low, high, p, (Stree.empty _) => false
  | low, high, p, (Stree.leaf y _ _) => (x = y)
  | low, high, p, (Stree.node y left right) => by sorry

def Stree.size {α : Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Stree α p → Nat
  | low, high, p, (Stree.empty _) => 0
  | low, high, p, (Stree.leaf x _ _) => 1
  | low, high, p, (Stree.node x left right) => 1 + Stree.size left + Stree.size right

theorem Stree.elem_low {α : Type} [LinearOrder α] (x : α)
  {low high : Bounded α} {p : low < high} (t : Stree α p) :
  Stree.elem x t = tt → low < element x := by
  sorry
  -- induction t with _ _ _ _ _ _ _ _ _ _ y,
  -- { obviously },
  -- { obviously },
  -- { apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [Stree.elem, decidable.lt_by_cases, xy], obviously },
  --   { intro xy, obviously },
  --   { intro yx, simp [Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], intro, transitivity' y, obviously }
  -- }

theorem Stree.elem_high {α : Type} [LinearOrder α] (x : α)
  {low high : Bounded α} {p : low < high} (t : Stree α p) :
  Stree.elem x t = tt → element x < high := by
  sorry
  -- induction t with _ _ _ A B C D E low high y I J left right ih_right ih_left,
  -- { obviously },
  -- { obviously },
  -- { apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [Stree.elem, decidable.lt_by_cases, xy], intro, transitivity' y, obviously },
  --   { intro xy, obviously },
  --   { intro yx, simp [Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], obviously }
  -- }


@[reducible]
def Stree.insert {α : Type} [LinearOrder α] (x : α) :
  ∀ {low high : Bounded α} {p : low < high} (t : Stree α p), low < element x → element x < high → Stree α p
  | low, high, p, (Stree.empty _), lowx, xhigh => Stree.leaf x lowx xhigh
  | low, high, p, (Stree.leaf y lowy yhigh), lowx, xhigh => sorry
      -- Decidable.lt_by_cases x y
      --   (fun xy => Stree.node y (Stree.leaf x lowx xy) (Stree.empty yhigh))
      --   (fun _ => Stree.leaf y lowy yhigh)
      --   (fun yx => Stree.node y (Stree.empty lowy) (Stree.leaf x yx xhigh))
  | low, high, p, (Stree.node y left right), lowx, xhigh => sorry
      -- decidable.lt_by_cases x y
      --   (fun xy => Stree.node y (@Stree.insert _ y _ left lowx xy) right)
      --   (fun _ => Stree.node y left right)
      --   (fun yx => Stree.node y left (@Stree.insert y _ _ right yx xhigh))

lemma elem_insert (α : Type) [LinearOrder α] (x : α) {low high : Bounded α}
  {lowx : low < element x} {xhigh : element x < high} (t : Stree α (lt_trans lowx xhigh)) :
  Stree.elem x (Stree.insert x t lowx xhigh) := by
  sorry
  -- induction t with _ _ _ _ _ y _ _ _ _ y _ _ _ _ ih_left ih_right,
  -- { simp },
  -- { apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy] },
  --   { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy] },
  --   { intro yx, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, lt_asymm, yx] }
  -- },
  -- { apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy], apply ih_left },
  --   { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy, lt_irrefl] },
  --   { intro yx, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, lt_asymm, yx], apply ih_right }
  -- } 

@[reducible]
def Stree.forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), Bool
  | _, _, _, (Stree.empty _) => true
  | _, _, _, (Stree.leaf x _ _) => Decidable.decide (p x)
  | _, _, _, (Stree.node x left right) => 
    Decidable.decide (p x) && Stree.forall p left && Stree.forall p right

def Stree.option_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
  ∀ {low high : Bounded α} {b : low < high} (t : Option (Stree α b)), Bool
  | _, _, _, none => false
  | _, _, _, (some t) => Stree.forall p t

lemma Stree.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
  Stree.forall p t = tt → ∀ (x : α), Stree.elem x t → p x :=  by
  sorry
  -- intros low high b t,
  -- induction t with _ _ _ _ _ _ _ _ _ _  y,
  -- { simp },
  -- { simp [Stree.forall] },
  -- { simp [Stree.forall], intros py lall rall x,
  --   apply (decidable.lt_by_cases x y),
  --   { intro xy, simp [ Stree.elem, decidable.lt_by_cases, xy], tautology },
  --   { intro xy, simp [ Stree.elem, decidable.lt_by_cases, xy], assumption },
  --   { intro yx, simp [ Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], tautology },
  -- }

@[reducible]
def Stree.exists {α : Type} [LinearOrder α] :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b) (p : α → Bool), Bool
  | _, _, _, (Stree.empty _), _ => false
  | _, _, _, (Stree.leaf x _ _), p => p x
  | _, _, _, (Stree.node x left right), p => p x || Stree.exists left p || Stree.exists right p

lemma Stree.exists_is_exists {α : Type} [LinearOrder α] (p : α → Bool) :
  ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
  Stree.exists t p = tt → ∃ (x : α), Stree.elem x t ∧ p x := by
  sorry
  -- intros low high b t,
  -- induction t with low high lh D E F G H I J y L M left right ih_left ih_right,
  -- { simp [Stree.exists] },
  -- { simp [Stree.exists] },
  -- { simp, intro h, cases h with h1 ept,
  --   { cases h1 with pyt ept, 
  --     { existsi y, simp [pyt, Stree.elem, decidable.lt_by_cases] },
  --     { obtain ⟨z, zleft, pz⟩ := ih_left ept,
  --       existsi z,
  --       have zy : z < y := Stree.elem_high z left zleft,
  --       simp [Stree.elem, decidable.lt_by_cases, zy], tautology
  --     }
  --   },
  --   { obtain ⟨z, zright, pz⟩ := ih_right ept,
  --     existsi z,
  --     have yz : y < z := Stree.elem_low z right zright,
  --     simp [Stree.elem, decidable.lt_by_cases, yz, lt_asymm yz], tautology }
  -- }

def Stree.intersection {α : Type} [LinearOrder α] :
  ∀ {low high : Bounded α} {b : low < high},
  Stree α b → Stree α b → Stree α b
| _, _, b, (Stree.empty _), t => Stree.empty b
| _, _, b, t, (Stree.empty _) => Stree.empty b
| _, _, b, (Stree.leaf x _ _), (Stree.leaf y _ _) => if x = y then (Stree.leaf x _ _) else Stree.empty b
| _, _, b, (Stree.node x left right), (Stree.leaf y _ _) => 
    if x = y then (Stree.leaf x _ _) 
    else if Stree.elem y left then (Stree.leaf y _ _)
    else if Stree.elem y right then (Stree.leaf y _ _)
    else Stree.empty b
| _, _, b, (Stree.leaf x _ _), (Stree.node y left right) =>
    if x = y then (Stree.leaf x _ _) 
    else if Stree.elem x left then (Stree.leaf x _ _)
    else if Stree.elem x right then (Stree.leaf x _ _)
    else Stree.empty b
| _, _, b, (Stree.node x left right), t =>  sorry

def Tset (α : Type) [lo : LinearOrder α] := @Stree α lo bottom top (by rfl)

def Tset.mem {α : Type} [LinearOrder α] (x : α) (t : Tset α) := Stree.elem x t

def Tset.option_mem {α : Type} [LinearOrder α] (x : α) : Option (Tset α) → Bool
  | none => false
  | (some t) => Tset.mem x t
  

instance Tset.has_mem {α : Type} [LinearOrder α]: Membership α (Tset α) where
  mem := fun x t => Tset.mem x t
  
instance Tset.option_has_mem {α : Type} [LinearOrder α] : Membership α (Option (Tset α)) where
  mem := fun x t => Tset.option_mem x t

instance Tset.has_insert {α : Type} [LinearOrder α]: Insert α (Tset α) where
  insert := fun x t => Stree.insert x t rfl rfl 

def Tset.add {α : Type} [LinearOrder α] (x : α) (t : Tset α) := Stree.insert x t (_) (_)

lemma Tset.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
  ∀ (t : Tset α), Stree.forall p t = tt → ∀ (x : α), x ∈ t → p x :=
  by apply Stree.forall_is_forall

-- -- def Tset.intersection {α : Type} [LinearOrder α] : Tset α → Tset α → Tset α := sorry
end TreeSet

-- import order.lexicographic
-- import data.fintype.basic
-- import tactic
-- -- Extension of an order with a new bottom and top elements. 
-- namespace tree_set

-- inductive Bounded (α : Type) : Type
-- | bottom : Bounded
-- | element : α -> Bounded
-- | top : Bounded

-- open Bounded

-- instance Bounded_has_coe (α : Type) : has_coe α (Bounded α) =>
--   { coe := element }

-- @[simp, reducible]
-- def Bounded_le {α : Type} [has_le α] : Bounded α → Bounded α → Prop
--   | bottom _ := true
--   | (element _) bottom := false
--   | (element x) (element y) := (x ≤ y)
--   | (element _) top := true
--   | top bottom := false
--   | top (element _) := false
--   | top top := true

-- instance Bounded_has_le (α : Type) [has_le α] : has_le (Bounded α) :=
--   { le := Bounded_le }

-- @[simp, reducible]
-- def Bounded_lt {α : Type} [has_lt α] : Bounded α → Bounded α → Prop
--   | bottom bottom := false
--   | bottom (element _) := true
--   | bottom top := true
--   | (element _) bottom := false
--   | (element x) (element y) := (x < y)
--   | (element _) top := true
--   | top _ := false

-- instance Bounded_has_lt (α : Type) [has_lt α] : has_lt (Bounded α) :=
--   { lt := Bounded_lt }

-- lemma Bounded_le_trans {α : Type} [preorder α] {a b c : Bounded α} :
--   Bounded_le a b → Bounded_le b c → Bounded_le a c :=
-- begin
--   cases_matching* (Bounded α) ; try { tautology },
--   apply le_trans
-- end

-- instance Bounded_preorder (α : Type) [preorder α] : preorder (Bounded α) :=
--   { lt := Bounded_lt,
--     le := Bounded_le,
--     le_refl := by { intro a, cases a ; trivial },
--     le_trans := by { apply Bounded_le_trans },
--     lt_iff_le_not_le := by { intros a b, cases a ; cases b ; tautology <|>  apply lt_iff_le_not_le }
--   }

-- instance Bounded_partial_order (α : Type) [partial_order α]: partial_order (Bounded α) :=
--   { le_antisymm :=
--       by { intros a b,  cases a ; cases b ; try { tautology },
--            intros ab ba, congr, apply (le_antisymm ab ba) },
--     .. tree_set.Bounded_preorder α }

-- instance Bounded_LinearOrder (α : Type) [LinearOrder α] : LinearOrder (Bounded α) :=
--   { le_total := by { intros a b, cases a ; cases b ; try { tautology }, apply le_total },
--     decidable_le := by { intros a b, cases a ; cases b ; apply_instance },
--     .. tree_set.Bounded_partial_order α
--   }

-- inductive Stree (α : Type) [LinearOrder α] : ∀ {low high : Bounded α}, low < high → Type
-- | empty : ∀ {low high} (p : low < high), Stree p
-- | leaf : ∀ {low high} (x : α) (lowx : low < element x) (xhigh : element x < high), Stree (lt_trans lowx xhigh)
-- | node : ∀ {low high} (x : α) {q : low < element x} {r : element x < high}
--            (left : Stree q) (right : Stree r), Stree (lt_trans q r)


-- example: Stree ℕ (by { trivial } : bottom < top) :=
--   Stree.node 20 
--     (Stree.empty true.intro)
--     (Stree.leaf 42 (by { norm_num } : 20 < 42) true.intro)

-- @[reducible]
-- def Stree.elem {α : Type} [LinearOrder α] (x : α) :
--     ∀ {low high : Bounded α} {p : low < high}, Stree α p → bool
-- | low high p (Stree.empty _) := ff
-- | low high p (Stree.leaf y _ _) := (x = y)
-- | low high p (Stree.node y left right) :=
--     decidable.lt_by_cases x y
--       (λ _, Stree.elem left)
--       (λ _, tt)
--       (λ _, Stree.elem right)

-- def Stree.size {α : Type} [LinearOrder α] : ∀ {low high : Bounded α} {p : low < high}, Stree α p → ℕ
-- | low high p (Stree.empty _) := 0
-- | low high p (Stree.leaf x _ _) := 1
-- | low high p (Stree.node x left right) := 1 + Stree.size left + Stree.size right

-- theorem Stree.elem_low {α : Type} [LinearOrder α] (x : α)
--   {low high : Bounded α} {p : low < high} (t : Stree α p) :
--   Stree.elem x t = tt → low < element x :=
-- begin
--   induction t with _ _ _ _ _ _ _ _ _ _ y,
--   { obviously },
--   { obviously },
--   { apply (decidable.lt_by_cases x y),
--     { intro xy, simp [Stree.elem, decidable.lt_by_cases, xy], obviously },
--     { intro xy, obviously },
--     { intro yx, simp [Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], intro, transitivity' y, obviously }
--   }
-- end

-- theorem Stree.elem_high {α : Type} [LinearOrder α] (x : α)
--   {low high : Bounded α} {p : low < high} (t : Stree α p) :
--   Stree.elem x t = tt → element x < high :=
-- begin
--   induction t with _ _ _ A B C D E low high y I J left right ih_right ih_left,
--   { obviously },
--   { obviously },
--   { apply (decidable.lt_by_cases x y),
--     { intro xy, simp [Stree.elem, decidable.lt_by_cases, xy], intro, transitivity' y, obviously },
--     { intro xy, obviously },
--     { intro yx, simp [Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], obviously }
--   }
-- end

-- @[reducible]
-- def Stree.insert {α : Type} [LinearOrder α] (x : α) :
--   ∀ {low high : Bounded α} {p : low < high} (t : Stree α p), low < element x → element x < high → Stree α p
-- | low high p (Stree.empty _) lowx xhigh := Stree.leaf x lowx xhigh
-- | low high p (Stree.leaf y lowy yhigh) lowx xhigh :=
--     decidable.lt_by_cases x y
--       (λ xy, Stree.node y (Stree.leaf x lowx xy) (Stree.empty yhigh))
--       (λ _, Stree.leaf y lowy yhigh)
--       (λ yx, Stree.node y (Stree.empty lowy) (Stree.leaf x yx xhigh))
-- | low high p (Stree.node y left right) lowx xhigh :=
--     decidable.lt_by_cases x y
--       (λ xy, Stree.node y (@Stree.insert _ y _ left lowx xy) right)
--       (λ _, Stree.node y left right)
--       (λ yx, Stree.node y left (@Stree.insert y _ _ right yx xhigh))

-- lemma elem_insert (α : Type) [LinearOrder α] (x : α) {low high : Bounded α}
--   {lowx : low < element x} {xhigh : element x < high} (t : Stree α (lt_trans lowx xhigh)) :
--   Stree.elem x (Stree.insert x t lowx xhigh) :=
-- begin
--   induction t with _ _ _ _ _ y _ _ _ _ y _ _ _ _ ih_left ih_right,
--   { simp },
--   { apply (decidable.lt_by_cases x y),
--     { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy] },
--     { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy] },
--     { intro yx, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, lt_asymm, yx] }
--   },
--   { apply (decidable.lt_by_cases x y),
--     { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy], apply ih_left },
--     { intro xy, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, xy, lt_irrefl] },
--     { intro yx, simp [Stree.elem, Stree.insert, decidable.lt_by_cases, lt_asymm, yx], apply ih_right }
--   } 
-- end

-- @[reducible]
-- def Stree.forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
--   ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), bool
-- | _ _ _ (Stree.empty _) := tt
-- | _ _ _ (Stree.leaf x _ _):= decidable.to_bool (p x)
-- | _ _ _ (Stree.node x left right) := 
--   decidable.to_bool (p x) && Stree.forall left && Stree.forall right

-- def Stree.option_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p] :
--   ∀ {low high : Bounded α} {b : low < high} (t : option (Stree α b)), bool
-- | _ _ _ none := ff
-- | _ _ _ (some t) := Stree.forall p t

-- lemma Stree.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
--   ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
--   Stree.forall p t = tt → ∀ (x : α), Stree.elem x t → p x :=  
-- begin
--   intros low high b t,
--   induction t with _ _ _ _ _ _ _ _ _ _  y,
--   { simp },
--   { simp [Stree.forall] },
--   { simp [Stree.forall], intros py lall rall x,
--     apply (decidable.lt_by_cases x y),
--     { intro xy, simp [ Stree.elem, decidable.lt_by_cases, xy], tautology },
--     { intro xy, simp [ Stree.elem, decidable.lt_by_cases, xy], assumption },
--     { intro yx, simp [ Stree.elem, decidable.lt_by_cases, yx, lt_asymm yx], tautology },
--   }
-- end

-- @[reducible]
-- def Stree.exists {α : Type} [LinearOrder α] :
--   ∀ {low high : Bounded α} {b : low < high} (t : Stree α b) (p : α → bool), bool
-- | _ _ _ (Stree.empty _) _ := ff
-- | _ _ _ (Stree.leaf x _ _) p := p x
-- | _ _ _ (Stree.node x left right) p := p x || Stree.exists left p || Stree.exists right p

-- lemma Stree.exists_is_exists {α : Type} [LinearOrder α] (p : α → bool) :
--   ∀ {low high : Bounded α} {b : low < high} (t : Stree α b), 
--   Stree.exists t p = tt → ∃ (x : α), Stree.elem x t ∧ p x :=  
-- begin
--   intros low high b t,
--   induction t with low high lh D E F G H I J y L M left right ih_left ih_right,
--   { simp [Stree.exists] },
--   { simp [Stree.exists] },
--   { simp, intro h, cases h with h1 ept,
--     { cases h1 with pyt ept, 
--       { existsi y, simp [pyt, Stree.elem, decidable.lt_by_cases] },
--       { obtain ⟨z, zleft, pz⟩ := ih_left ept,
--         existsi z,
--         have zy : z < y := Stree.elem_high z left zleft,
--         simp [Stree.elem, decidable.lt_by_cases, zy], tautology
--       }
--     },
--     { obtain ⟨z, zright, pz⟩ := ih_right ept,
--       existsi z,
--       have yz : y < z := Stree.elem_low z right zright,
--       simp [Stree.elem, decidable.lt_by_cases, yz, lt_asymm yz], tautology }
--   }
-- end

-- -- def Stree.intersection {α : Type} [LinearOrder α] :
-- --   ∀ {low high : Bounded α} {b : low < high},
-- --   Stree α b → Stree α b → Stree α b
-- -- | _ _ b (Stree.empty _) t := Stree.empty b
-- -- | _ _ b t (Stree.empty _) := Stree.empty b
-- -- | _ _ b (Stree.leaf x _ _) (Stree.leaf y _ _) := if x = y then (Stree.leaf x _ _) else Stree.empty b
-- -- | _ _ b (Stree.node x left right) (Stree.leaf y _ _) := 
-- --     if x = y then (Stree.leaf x _ _) 
-- --     else if Stree.elem y left then (Stree.leaf y _ _)
-- --     else if Stree.elem y right then (Stree.leaf y _ _)
-- --     else Stree.empty b
-- -- | _ _ b (Stree.leaf x _ _) (Stree.node y left right) :=
-- --     if x = y then (Stree.leaf x _ _) 
-- --     else if Stree.elem x left then (Stree.leaf x _ _)
-- --     else if Stree.elem x right then (Stree.leaf x _ _)
-- --     else Stree.empty b
-- -- | _ _ b (Stree.node x left right) t :=  sorry

-- def Tset (α : Type) [lo : LinearOrder α] := @Stree α lo bottom top true.intro

-- def Tset.mem {α : Type} [LinearOrder α] (x : α) (t : Tset α) := Stree.elem x t

-- def Tset.option_mem {α : Type} [LinearOrder α] (x : α) : option (Tset α) → bool
-- | none := ff
-- | (some t) := Tset.mem x t

-- instance Tset.has_mem {α : Type} [LinearOrder α]: has_mem α (Tset α) :=
--   { mem := λ x t, Tset.mem x t }

-- instance Tset.option_has_mem {α : Type} [LinearOrder α] : has_mem α (option (Tset α)) :=
--   { mem := λ x t, Tset.option_mem x t }

-- instance Tset.has_insert {α : Type} [LinearOrder α]: has_insert α (Tset α) :=
--   { insert := λ x t, Stree.insert x t true.intro true.intro }

-- def Tset.add {α : Type} [LinearOrder α] (x : α) (t : Tset α) := Stree.insert x t true.intro true.intro

-- lemma Tset.forall_is_forall {α : Type} [LinearOrder α] (p : α → Prop) [DecidablePred p]:
--   ∀ (t : Tset α), Stree.forall p t = tt → ∀ (x : α), x ∈ t → p x :=
--   by apply Stree.forall_is_forall

-- -- def Tset.intersection {α : Type} [LinearOrder α] : Tset α → Tset α → Tset α := sorry

-- end tree_set