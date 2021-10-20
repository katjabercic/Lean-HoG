import combinatorics.simple_graph.basic

namespace hog

-- open tactic
-- open tactic.interactive
-- open interactive (parse)
-- open interactive.types (texpr)
-- open lean.parser (ident)

def neighbor_relation : Type := list (ℕ × list ℕ)
def adjacency_list: Type := list (ℕ × ℕ)
def preadjacency := ℕ → ℕ → bool


structure hog : Type :=
 (neighborhoods : neighbor_relation)
 (preadjacency : ℕ → ℕ → Prop)
 (graph : simple_graph ℕ)
--  (number_of_vertices_eq_size : raw.number_of_vertices = some (hog.size raw))


-- meta def roast (e : parse texpr) : tactic unit :=
-- do { t ← tactic.i_to_expr ``((%%e).number_of_vertices = some (hog.size %%e)),
--      (_, p) ← solve_aux t (tactic.reflexivity),
--      r ← i_to_expr_strict ``(hog.mk %%e %%p),
--      exact r
--    }
   
-- #check list.head hog.db_001
-- def hogs : list (list hog) := list.map (λ (rh : hog.raw_hog), by roast rh) (list.head hog.db_001)

end hog