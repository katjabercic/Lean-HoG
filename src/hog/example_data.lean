import .tactic
import .graph
import .path
import .tree_representation

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


def cycle3_tree : BT (lex ℕ ℕ) := BT.node (2,1) (BT.leaf (1,3)) (BT.leaf (3,4))

#eval BT.is_bst cycle3_tree

def G1 : BT (lex ℕ ℕ) := BT.node (1,4) (BT.node (1,3) (BT.leaf (1,2)) BT.empty) (BT.node (2,3) BT.empty (BT.leaf (3,4)))
def G2 : BT (lex ℕ ℕ) := BT.node (1, 4) (BT.node (1, 3) (BT.leaf (1, 2)) (BT.empty)) (BT.node (3, 4) (BT.leaf (2, 3)) (BT.empty))

def G1_bst : BST (lex ℕ ℕ) :=
{ tree := BT.node (1,4) (BT.node (1,3) (BT.leaf (1,2)) BT.empty) (BT.node (2,3) BT.empty (BT.leaf (3,4))),
  is_bst := by bool_reflect
}

end hog

