import .tactic
import .graph
import .path
import .component
import .tree_representation
import .tactic

namespace hog

def cycle3 : simple_irreflexive_graph :=
  from_edge_list 3 [(0,1), (1,2), (2,0)]

#check cycle3

instance: hog_edge_size cycle3 := ⟨ 3, rfl ⟩

#check max_degree cycle3


def hog2_BST : BST Edge :=
{ tree := BT.node {edge := (2, 3)} (BT.node {edge := (1, 4)} (BT.leaf {edge := (0, 4)}) (BT.empty)) (BT.leaf {edge := (3, 4)}),
  is_bst := begin simp, bool_reflect end
}

def hog2 : simple_irreflexive_graph := from_BST 5 hog2_BST

#eval hog2.vertex_size

set_option trace.eqn_compiler.elim_match true

lemma edge_4_1 : @decidable.to_bool 
  (hog2.edge (fin.mk 4 (by bool_reflect)) (fin.mk 1 (by bool_reflect))) 
  (hog2.edge_decidable (fin.mk 4 (by bool_reflect)) (fin.mk 1 (by bool_reflect))) 
  = tt := by refl

lemma edge_3_2 : @decidable.to_bool 
  (hog2.edge (fin.mk 3 (by bool_reflect)) (fin.mk 2 (by bool_reflect))) 
  (hog2.edge_decidable (fin.mk 3 (by bool_reflect)) (fin.mk 2 (by bool_reflect))) 
  = tt := by refl

lemma edge_4_3 : @decidable.to_bool 
  (hog2.edge (fin.mk 4 (by bool_reflect)) (fin.mk 3 (by bool_reflect))) 
  (hog2.edge_decidable (fin.mk 4 (by bool_reflect)) (fin.mk 3 (by bool_reflect))) 
  = tt := by refl

lemma edge_0_4 : @decidable.to_bool 
  (hog2.edge (fin.mk 0 (by bool_reflect)) (fin.mk 4 (by bool_reflect))) 
  (hog2.edge_decidable (fin.mk 0 (by bool_reflect)) (fin.mk 4 (by bool_reflect))) 
  = tt := by refl

def witness : num_components_witness :=
let H : hog2.vertex_size = 5 := by bool_reflect in
{ G := hog2,
  num_components := 1,
  c := λ v, 0,
  h := λ v : fin hog2.vertex_size, 
    match v with
    | ⟨ 0, _ ⟩ := 0
    | ⟨ 1, _ ⟩ := 4
    | ⟨ 2, _ ⟩ := 3
    | ⟨ 3, _ ⟩ := 2
    | ⟨ 4, _ ⟩ := 1
    | ⟨ _ , cond ⟩ := 0
    end,
  connect_edges := λ u v h, begin bool_reflect end,
  root := λ i : fin 1, 
    match i with 
    | ⟨ 0, _ ⟩ := ⟨ 0, by bool_reflect ⟩
    | _ := ⟨ 0, by bool_reflect ⟩ 
    end,
  is_root := λ i,
    match i with
    | ⟨ 0, _ ⟩ := ⟨ by bool_reflect, by bool_reflect ⟩
    | _ := ⟨ sorry, sorry ⟩
    end,
  uniqueness_of_roots := λ v : fin hog2.vertex_size, 
    match v with
    | ⟨ 0, _ ⟩ := λ h, by bool_reflect
    | ⟨ 1, _ ⟩ := λ h, by contradiction
    | ⟨ 2, _ ⟩ := λ h, by contradiction
    | ⟨ 3, _ ⟩ := λ h, by contradiction
    | ⟨ 4, _ ⟩ := λ h, by contradiction
    | ⟨ _ , cond ⟩ := sorry
    end,
  next := λ v : fin hog2.vertex_size,
    match v with
    | ⟨ 0, _ ⟩ := ⟨ 0, by bool_reflect ⟩
    | ⟨ 1, _ ⟩ := ⟨ 4, by bool_reflect ⟩
    | ⟨ 2, _ ⟩ := ⟨ 3, by bool_reflect ⟩
    | ⟨ 3, _ ⟩ := ⟨ 4, by bool_reflect ⟩
    | ⟨ 4, _ ⟩ := ⟨ 0, by bool_reflect ⟩
    | _ := ⟨ 0, by bool_reflect ⟩
    end,
  height_cond := λ (v : fin hog2.vertex_size) hyp,
    match v with
    | ⟨ 0, cond ⟩ := 
      begin 
        by_contra, 
        have H : witness._match_1 ⟨0, cond⟩ = 0, 
        bool_reflect,
        sorry
      end
    | ⟨ 1, cond ⟩ :=
      begin
        split,
        apply (to_bool_iff (hog2.edge (fin.mk 4 _) (fin.mk 1 _))).mp,
        exact edge_4_1,
        bool_reflect
      end
    | ⟨ 2, _ ⟩ :=
      begin
        split,
        apply (to_bool_iff (hog2.edge (fin.mk 3 _) (fin.mk 2 _))).mp,
        exact edge_3_2,
        bool_reflect
      end 
    | ⟨ 3, _ ⟩ :=
      begin
        split,
        apply (to_bool_iff (hog2.edge (fin.mk 4 _) (fin.mk 3 _))).mp,
        exact edge_4_3,
        bool_reflect
      end 
    | ⟨ 4, _ ⟩ :=
      begin
        split,
        apply (to_bool_iff (hog2.edge (fin.mk 0 _) (fin.mk 4 _))).mp,
        exact edge_0_4,
        bool_reflect
      end 
    | _ := sorry
    end,
}

def hog2_components_witness : number_of_connected_components := witness_components witness

#check hog2_components_witness

end hog

