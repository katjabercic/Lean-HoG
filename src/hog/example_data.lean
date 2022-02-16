import .tactic
import .graph
import .component

namespace hog

def cycle3 : simple_irreflexive_graph :=
  from_edge_list 3 [(0,1), (1,2), (2,0)]

#check cycle3

instance: hog_edge_size cycle3 := ⟨ 3, rfl ⟩

#check max_degree cycle3

#check connected cycle3 (fin.mk 0 (nat.lt_of_sub_eq_succ rfl)) (fin.mk 1 (nat.lt_of_sub_eq_succ rfl))

-- instance: hog_max_degree cycle3 := ⟨ 2, rfl ⟩

-- instance: hog_min_degree cycle3 := ⟨ 2, rfl ⟩

-- instance: hog_regular cycle3 := ⟨ rfl ⟩

end hog

