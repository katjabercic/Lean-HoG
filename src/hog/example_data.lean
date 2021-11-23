import .tactic
import .graph

namespace hog

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

instance: hog_edge_size cycle3 := ⟨ 3, rfl ⟩

instance: hog_max_degree cycle3 := ⟨ 2, rfl ⟩

instance: hog_min_degree cycle3 := ⟨ 2, rfl ⟩

instance: hog_regular cycle3 := ⟨ rfl ⟩

end hog

