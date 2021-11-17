-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.

import .tactic

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edge : fin vertex_size → fin vertex_size → bool)
  (irreflexive : (∀ i, ¬ edge i i) . bool_reflect)
  (symmetric : (∀ i j, edge i j → edge j i) . bool_reflect)

def cycle3 : simple_irreflexive_graph :=
  { simple_irreflexive_graph .
    vertex_size := 3,
    edge :=
      (λ (i : fin 3) (j : fin 3),
        (match i.val, j.val with
        | 0, 1 := tt | 1, 0 := tt
        | 1, 2 := tt | 2, 1 := tt
        | 2, 0 := tt | 0, 2 := tt
        | _, _ := ff -- catch all case for false
        end : bool))     
  }