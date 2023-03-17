import Graph
import TreeSet
import TreeMap
import Tactic
import ConnectedComponents

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
lemma helper2 : Bounded.element (Edge.mk (0, 1)) < Bounded.element (Edge.mk (0,2)) := by bool_reflect
lemma helper3 : Bounded.element (Edge.mk (0, 2)) < Bounded.element (Edge.mk (1, 2)) := by bool_reflect
lemma helper4: Bounded.element (Edge.mk (1, 2)) < Bounded.top := by bool_reflect

def example_1: Tset Edge :=
  Stree.node { edge := (0,2) }
    (Stree.leaf { edge := (0,1) } (helper1) (helper2))
    (Stree.leaf { edge := (1,2) } (helper3) (helper4))

def temp0 : Tset Nat :=
  Stree.node 1
    (Stree.empty (by bool_reflect))
    (Stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp1 : Tset Nat :=
  Stree.node 0
    (Stree.empty (by bool_reflect))
    (Stree.leaf 2 (by bool_reflect) (by bool_reflect))

def temp2 : Tset Nat :=
  Stree.node 0
    (Stree.empty (by bool_reflect))
    (Stree.leaf 1 (by bool_reflect) (by bool_reflect))

def N₁ : Tmap Nat (Tset Nat) :=
  Smap.node 1 temp1
    (Smap.leaf 0 temp0 (by bool_reflect) (by bool_reflect))
    (Smap.leaf 2 temp2 (by bool_reflect) (by bool_reflect))


def g : SimpleIrreflexiveGraph := {
  vertexSize := 3,
  edges := example_1,
  edgeSize := 3,
  edgeSizeCorrect := by rfl,
  neighborhoods := N₁,
  neighborhoodsCorrect := by rfl
}

lemma foos : (Edge.mk (0,1)) ∈ g.edges := by
  simp  

def w : numComponentsWitness := {
  G := g,
  numComponents := 1,
  c := fun v =>
    match v with
      | 0 => 0
      | 1 => 0
      | 2 => 0
      | _ => 0
  h := fun v =>
    match v with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | _ => 0
  connectEdges := by
      apply Tset.forallIsForall
      bool_reflect
  root := fun (v : Fin 1) =>
    match v with
    | ⟨ 0, _ ⟩ => 0
    | _ => 0
  isRoot := fun i =>
    match i with
    | ⟨ 0, _ ⟩ => by bool_reflect
    | i => sorry
  uniquenessOfRoots := fun v =>
    match v with
    | 0 => by bool_reflect
    | 1 => by simp
    | 2 => by simp
    | _ => sorry
  next := fun v =>
    match v with
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | _ => 0
  heightCond := fun v =>
    match v with
    | 0 => by
        have nh : ¬ 0 < 0 := irrefl 0
        simp
    | 1 => by
        intro h
        simp [edgeRelation, lt_by_cases]
    | 2 => by
        intro h
        simp [edgeRelation, lt_by_cases]
    | _ => sorry
}

lemma wc : numberOfConnectedComponents := witnessComponents w

end hog

