-- import Mathlib.Init.Data.Bool.Lemmas
import Graph
import TreeSet
import TreeMap
import Tactic

namespace hog

open TreeSet
open TreeMap
open Tactic

def edge_1 : Edge := { edge := (0,2), src_lt_trg := by trivial }
def edge_2 : Edge := { edge := (0,1), src_lt_trg := by trivial }


instance compareEdgeDecidable (e1 e2 : Edge) : Decidable (e1 < e2) := by
  have l : LinearOrder Edge := by apply EdgeLinearOrder
  have r := l.decidable_lt
  have q := r e1 e2
  simp at q
  -- exact q
  sorry

set_option pp.analyze.checkInstances true in
lemma foo :  ({ edge := (0,2), src_lt_trg := by trivial } : Edge) < ({ edge := (0,1), src_lt_trg := by trivial }: Edge) := by
  have l : LinearOrder Edge := by apply EdgeLinearOrder
  apply Bool.of_decide_true
  sorry

  
def example_1: Tset Edge :=
  Stree.node { edge := (0,2) }
    (Stree.leaf { edge := (0,1) } (by trivial) (by sorry))
    (Stree.leaf { edge := (1,2) } (by sorry) (by sorry))

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

