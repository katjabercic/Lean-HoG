import .tactic
import .graph
import .connected_component
import .tree_set
import .tree_map

namespace hog

open tree_set
open tree_map

def example_1: tset Edge :=
  stree.node { edge := (0,2) }
    (stree.leaf { edge := (0,1) } (by bool_reflect) (by bool_reflect))
    (stree.leaf { edge := (1,2) } (by bool_reflect) (by bool_reflect))

def temp0 : tset ℕ :=
  stree.node 1
    (stree.empty (by bool_reflect))
    (stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp1 : tset ℕ :=
  stree.node 0
    (stree.empty (by bool_reflect))
    (stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp2 : tset ℕ :=
  stree.node 0
    (stree.empty (by bool_reflect))
    (stree.leaf 1 (by bool_reflect) (by bool_reflect))

def N₁ : tmap ℕ (tset ℕ) :=
  smap.node 1 temp1
    (smap.leaf 0 temp0 (by bool_reflect) (by bool_reflect))
    (smap.leaf 2 temp2 (by bool_reflect) (by bool_reflect))

def g : simple_irreflexive_graph := 
{ vertex_size := 3,
  edges := example_1,
  edge_size := 3,
  edge_size_correct := by refl,
  neighborhoods := N₁,
  neighborhoods_correct := by refl
}

def w : num_components_witness := { 
  G := g,
  num_components := 1,
  c := λ v : ℕ, 
    match v with
    | 0 := 0
    | 1 := 0
    | 2 := 0
    | _ := 0
    end,
  h := λ v, 
    match v with
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | _ := 0
    end,
  connect_edges := 
    begin 
      apply tset.forall_is_forall,
      bool_reflect
    end,
  root := λ (v : fin 1),
    match v with
    | ⟨ 0, _ ⟩ := 0
    | _ := 0
    end,
  is_root := λ i,
    match i with
    | ⟨ 0, _ ⟩ := by bool_reflect
    | i := sorry
    end,
  uniqueness_of_roots := λ v,
    match v with
    | 0 := by bool_reflect
    | 1 := by contradiction
    | 2 := by contradiction
    | _ := sorry
    end,
  next := λ v,
    match v with
    | 0 := 0
    | 1 := 0
    | 2 := 1
    | _ := 0
    end,
  height_cond := λ v,
    match v with
    | 0 := 
      begin
        have nh : ¬ 0 < 0 := irrefl 0,
        contradiction
      end
    | 1 := 
      begin 
        intro h,
        simp [edge_relation, decidable.lt_by_cases],
        bool_reflect
      end
    | 2 :=
      begin 
        intro h,
        simp [edge_relation, decidable.lt_by_cases],
        bool_reflect
      end
    | _ := sorry
    end
}

def wc : number_of_connected_components := witness_components w


end hog

