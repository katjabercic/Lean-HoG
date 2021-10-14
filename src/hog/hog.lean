import .raw_hog
import .data.hog_data_001
import tactic

open tactic
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident)

structure hog : Type :=
 (raw : hog.raw_hog)
 (number_of_vertices_eq_size : raw.number_of_vertices = some (hog.size raw))

meta def tactic.interactive.roast (e : parse texpr) : tactic unit :=
do { t ← tactic.i_to_expr ``((%%e).number_of_vertices = some (hog.size %%e)),
     (_, p) ← solve_aux t (tactic.reflexivity),
     r ← i_to_expr_strict ``(hog.mk %%e %%p),
     exact r
   }
   
-- #check list.head hog.db_001
-- def hogs : list (list hog) := list.map (λ (rh : hog.raw_hog), by roast rh) (list.head hog.db_001)
def hog1 : hog := by roast hog.raw_hog00001