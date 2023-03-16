-- import Mathlib.Init.Data.Bool.Lemmas
import Graph
import TreeSet
import TreeMap
import Tactic

namespace hog

open TreeSet
open TreeMap
open Tactic

def edge_1 : Edge := { edge := (0,1), src_lt_trg := by trivial }
def edge_2 : Edge := { edge := (0,2), src_lt_trg := by trivial }


instance compareEdgeDecidable (e1 e2 : Edge) : Decidable (e1 < e2) := by
  infer_instance

lemma foo :  ({ edge := (0,1), src_lt_trg := by trivial } : Edge) < ({ edge := (0,2), src_lt_trg := by trivial }: Edge) := by
  bool_reflect

lemma helper1 : Bounded.bottom < Bounded.element (Edge.mk (0, 1)) := by bool_reflect
  
lemma helper2 : Bounded.element (Edge.mk (0,1)) < Bounded.element (Edge.mk (0,2)) := by bool_reflect

lemma helper3 : Bounded.element (Edge.mk (0, 2)) < Bounded.element (Edge.mk (1, 2)) := by bool_reflect

lemma helper4: Bounded.element (Edge.mk (1, 2)) < Bounded.top := by bool_reflect

set_option pp.explicit false in
def example_1: Tset Edge :=
  Stree.node { edge := (0,2) }
    (Stree.leaf { edge := (0,1) } (helper1) (helper2))
    (Stree.leaf { edge := (1,2) } (helper3) (helper4))

def temp0 : Tset ℕ :=
  Stree.node 1
    (Stree.empty (by bool_reflect))
    (Stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp1 : Tset ℕ :=
  Stree.node 0
    (Stree.empty (by bool_reflect))
    (Stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp2 : Tset ℕ :=
  Stree.node 0
    (Stree.empty (by bool_reflect))
    (Stree.leaf 1 (by bool_reflect) (by bool_reflect))

def N₁ : Tmap ℕ (Tset ℕ) :=
  Smap.node 1 temp1
    (Smap.leaf 0 temp0 (by bool_reflect) (by bool_reflect))
    (Smap.leaf 2 temp2 (by bool_reflect) (by bool_reflect))


def g : SimpleIrreflexiveGraph := {
  vertexSize := 3,
  edges := example_1,
  edgeSize := 3,
  edgeSizeCorrect := by rfl,
  neighborhoods := N₁,
  neighborhoods_correct := by rfl
}

-- def w : num_components_witness := { 
--   G := g,
--   num_components := 1,
--   c := λ v : ℕ, 
--     match v with
--     | 0 := 0
--     | 1 := 0
--     | 2 := 0
--     | _ := 0
--     end,
--   h := λ v, 
--     match v with
--     | 0 := 0
--     | 1 := 1
--     | 2 := 2
--     | _ := 0
--     end,
--   connect_edges := 
--     begin 
--       apply tset.forall_is_forall,
--       bool_reflect
--     end,
--   root := λ (v : fin 1),
--     match v with
--     | ⟨ 0, _ ⟩ := 0
--     | _ := 0
--     end,
--   is_root := λ i,
--     match i with
--     | ⟨ 0, _ ⟩ := by bool_reflect
--     | i := sorry
--     end,
--   uniqueness_of_roots := λ v,
--     match v with
--     | 0 := by bool_reflect
--     | 1 := by contradiction
--     | 2 := by contradiction
--     | _ := sorry
--     end,
--   next := λ v,
--     match v with
--     | 0 := 0
--     | 1 := 0
--     | 2 := 1
--     | _ := 0
--     end,
--   height_cond := λ v,
--     match v with
--     | 0 := 
--       begin
--         have nh : ¬ 0 < 0 := irrefl 0,
--         contradiction
--       end
--     | 1 := 
--       begin 
--         intro h,
--         simp [edge_relation, decidable.lt_by_cases],
--         bool_reflect
--       end
--     | 2 :=
--       begin 
--         intro h,
--         simp [edge_relation, decidable.lt_by_cases],
--         bool_reflect
--       end
--     | _ := sorry
--     end
-- }

-- def wc : number_of_connected_components := witness_components w


end hog

