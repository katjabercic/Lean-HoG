import data.fintype.basic
import data.set.finite
import tactic

open tactic

-- This works
example: ∀ i : fin 3, i = i := (to_bool_iff _).mp rfl

-- This works
example: ∀ i : fin 3, i = i := by exact ((to_bool_iff _).mp rfl)

-- We define a tactic that will do precisely the same as above
meta def tactic.interactive.bool_reflect : tactic unit :=
do { p ← target,
     r ← i_to_expr ``((to_bool_iff %%(p)).mp rfl),
     exact r
    }

-- And now this does not work
example: ∀ i : fin 3, i = i := by bool_reflect
