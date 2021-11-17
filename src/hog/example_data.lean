import .tactic

namespace hog

def cycle3 : simple_graph (fin 3) :=
by from_adjacency 3 with
  λ (i : ℕ) (j : ℕ), (match i, j with
  | 0, 1 := tt | 1, 0 := tt
  | 1, 2 := tt | 2, 1 := tt
  | 2, 0 := tt | 0, 2 := tt
  | _, _ := ff -- catch all case for false
  end : bool)

end hog

