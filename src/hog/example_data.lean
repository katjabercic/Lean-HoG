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

def hog_00002 : simple_irreflexive_graph := from_BST 5 hog2_BST

lemma edge_4_1 : @decidable.to_bool
  (hog_00002.edge (fin.mk 4 (by bool_reflect)) (fin.mk 1 (by bool_reflect)))
  (hog_00002.edge_decidable (fin.mk 4 (by bool_reflect)) (fin.mk 1 (by bool_reflect)))
  = tt := by refl

lemma edge_3_2 : @decidable.to_bool
  (hog_00002.edge (fin.mk 3 (by bool_reflect)) (fin.mk 2 (by bool_reflect)))
  (hog_00002.edge_decidable (fin.mk 3 (by bool_reflect)) (fin.mk 2 (by bool_reflect)))
  = tt := by refl

lemma edge_4_3 : @decidable.to_bool
  (hog_00002.edge (fin.mk 4 (by bool_reflect)) (fin.mk 3 (by bool_reflect)))
  (hog_00002.edge_decidable (fin.mk 4 (by bool_reflect)) (fin.mk 3 (by bool_reflect)))
  = tt := by refl

lemma edge_0_4 : @decidable.to_bool
  (hog_00002.edge (fin.mk 0 (by bool_reflect)) (fin.mk 4 (by bool_reflect)))
  (hog_00002.edge_decidable (fin.mk 0 (by bool_reflect)) (fin.mk 4 (by bool_reflect)))
  = tt := by refl

def hog_00002_witness : num_components_witness :=
let H : hog_00002.vertex_size = 5 := by bool_reflect in
{ G := hog_00002,
  num_components := 1,
  c := λ v : fin hog_00002.vertex_size,
    match v with
    | ⟨ 0, _ ⟩ := 0
    | ⟨ 1, _ ⟩ := 0
    | ⟨ 2, _ ⟩ := 0
    | ⟨ 3, _ ⟩ := 0
    | ⟨ 4, _ ⟩ := 0
    | ⟨ _ , cond ⟩ := 0
    end,
  h := λ v : fin hog_00002.vertex_size,
    match v with
    | ⟨ 0, _ ⟩ := 0
    | ⟨ 1, _ ⟩ := 4
    | ⟨ 2, _ ⟩ := 3
    | ⟨ 3, _ ⟩ := 2
    | ⟨ 4, _ ⟩ := 1
    | ⟨ _ , cond ⟩ := 0
    end,
  connect_edges := λ u v : fin hog_00002.vertex_size,
    match u, v with
    | ⟨ 0, _ ⟩, ⟨ 0, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 0, _ ⟩, ⟨ 1, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 0, _ ⟩, ⟨ 2, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 0, _ ⟩, ⟨ 3, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 0, _ ⟩, ⟨ 4, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 1, _ ⟩, ⟨ 0, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 1, _ ⟩, ⟨ 1, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 1, _ ⟩, ⟨ 2, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 1, _ ⟩, ⟨ 3, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 1, _ ⟩, ⟨ 4, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 2, _ ⟩, ⟨ 0, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 2, _ ⟩, ⟨ 1, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 2, _ ⟩, ⟨ 2, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 2, _ ⟩, ⟨ 3, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 2, _ ⟩, ⟨ 4, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 3, _ ⟩, ⟨ 0, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 3, _ ⟩, ⟨ 1, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 3, _ ⟩, ⟨ 2, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 3, _ ⟩, ⟨ 3, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 3, _ ⟩, ⟨ 4, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 4, _ ⟩, ⟨ 0, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 4, _ ⟩, ⟨ 1, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 4, _ ⟩, ⟨ 2, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 4, _ ⟩, ⟨ 3, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ 4, _ ⟩, ⟨ 4, _ ⟩ := begin intro _, bool_reflect end
    | ⟨ _, _ ⟩, ⟨ _, _ ⟩ := sorry
    end,
  root := λ i : fin 1,
    match i with
    | ⟨ 0, _ ⟩ := ⟨ 0, by bool_reflect ⟩
    | _ := ⟨ 0, by bool_reflect ⟩
    end,
  is_root := λ i : fin 1,
    match i with
    | ⟨ 0, _ ⟩ := ⟨ by bool_reflect, by bool_reflect ⟩
    | _ := ⟨ sorry, sorry ⟩
    end,
  uniqueness_of_roots := λ v : fin hog_00002.vertex_size,
    match v with
    | ⟨ 0, _ ⟩ := by bool_reflect
    | ⟨ 1, _ ⟩ := by contradiction
    | ⟨ 2, _ ⟩ := by contradiction
    | ⟨ 3, _ ⟩ := by contradiction
    | ⟨ 4, _ ⟩ := by contradiction
    | ⟨ _ , cond ⟩ := sorry
    end,
  next := λ v : fin hog_00002.vertex_size,
    match v with
    | ⟨ 1, _ ⟩ := ⟨ 4, by bool_reflect ⟩
    | ⟨ 2, _ ⟩ := ⟨ 3, by bool_reflect ⟩
    | ⟨ 3, _ ⟩ := ⟨ 4, by bool_reflect ⟩
    | ⟨ 4, _ ⟩ := ⟨ 0, by bool_reflect ⟩
    | ⟨ _ , cond ⟩ := ⟨ 0, by bool_reflect ⟩
    end,
  height_cond := λ v : fin hog_00002.vertex_size,
    match v with
    | ⟨ 0, cond ⟩ :=
    begin
      intro h,
      by_contra,
      have H : hog_00002_witness._match_1 ⟨0, cond⟩ = 0,
      bool_reflect,
      sorry
    end
    | ⟨ 1, cond ⟩ :=
    begin
      intro h,
      split,
      apply (to_bool_iff (hog_00002.edge (fin.mk 4 _) (fin.mk 1 _))).mp,
      exact edge_4_1,
      bool_reflect
    end
    | ⟨ 2, cond ⟩ :=
    begin
      intro h,
      split,
      apply (to_bool_iff (hog_00002.edge (fin.mk 3 _) (fin.mk 2 _))).mp,
      exact edge_3_2,
      bool_reflect
    end
    | ⟨ 3, cond ⟩ :=
    begin
      intro h,
      split,
      apply (to_bool_iff (hog_00002.edge (fin.mk 4 _) (fin.mk 3 _))).mp,
      exact edge_4_3,
      bool_reflect
    end
    | ⟨ 4, cond ⟩ :=
    begin
      intro h,
      split,
      apply (to_bool_iff (hog_00002.edge (fin.mk 0 _) (fin.mk 4 _))).mp,
      exact edge_0_4,
      bool_reflect
    end
    | _ := sorry
    end,
}


def hog2_components_witness : number_of_connected_components := witness_components hog_00002_witness

#check hog2_components_witness

end hog
