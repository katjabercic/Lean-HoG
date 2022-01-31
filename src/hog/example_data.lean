import .tactic
import .graph

namespace hog

def cycle3 : simple_irreflexive_graph :=
  from_edge_list 3 [(0,1), (1,2), (2,0)]

-- instance: hog_edge_size cycle3 := ⟨ 3, rfl ⟩

-- instance: hog_max_degree cycle3 := ⟨ 2, rfl ⟩

-- instance: hog_min_degree cycle3 := ⟨ 2, rfl ⟩

-- instance: hog_regular cycle3 := ⟨ rfl ⟩

end hog

