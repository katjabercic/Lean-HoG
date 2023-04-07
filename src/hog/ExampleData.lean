import Mathlib.Data.Nat.Parity

import Graph
import TreeSet
import TreeMap
import Tactic
import ConnectedComponents
import Bipartite
import Walk
import Data.Invariants
import Data.Imports

namespace Hog

open TreeSet
open TreeMap
open Tactic
open Bipartite

def edge_1 : Edge := { edge := (0,1), src_lt_trg := by trivial }
def edge_2 : Edge := { edge := (0,2), src_lt_trg := by trivial }

instance compareEdgeDecidable (e1 e2 : Edge) : Decidable (e1 < e2) := by
  infer_instance

lemma foo :  ({ edge := (0,1), src_lt_trg := by trivial } : Edge) < ({ edge := (0,2), src_lt_trg := by trivial }: Edge) := by
  bool_reflect

lemma helper1 : Bounded.bottom < Bounded.element (Edge.mk (0, 1)) := by first | bool_reflect | rfl
lemma helper2 : Bounded.element (Edge.mk (0, 1)) < Bounded.element (Edge.mk (0,2)) := by bool_reflect
lemma helper3 : Bounded.element (Edge.mk (0, 2)) < Bounded.element (Edge.mk (1, 2)) := by bool_reflect
lemma helper4: Bounded.element (Edge.mk (1, 2)) < Bounded.top := by first | bool_reflect | rfl

-- Graph:
--      0
--    /   \
--   /     \
--  2 ----- 1
def example_1: Tset Edge :=
  Stree.node { edge := (0,2) }
    (Stree.leaf { edge := (0,1) } (helper1) (helper2))
    (Stree.leaf { edge := (1,2) } (helper3) (helper4))

def temp0 : Tset Nat :=
  Stree.node 1
    (Stree.empty (by first | bool_reflect | trivial))
    (Stree.leaf 2 (by bool_reflect) (by first | bool_reflect | trivial))

def temp1 : Tset Nat :=
  Stree.node 0
    (Stree.empty (by first | bool_reflect | rfl))
    (Stree.leaf 2 (by bool_reflect) (by first | bool_reflect | rfl))

def temp2 : Tset Nat :=
  Stree.node 0
    (Stree.empty (by first | bool_reflect | rfl))
    (Stree.leaf 1 (by bool_reflect) (by first | bool_reflect | rfl))

def superSet : Tset Nat :=
    Stree.node 1
    (Stree.leaf 0 (by rfl) (by bool_reflect))
    (Stree.leaf 2 (by bool_reflect) (by rfl))

def N₁ : Tmap Nat (Tset Nat) :=
  Smap.node 1 temp1
    (Smap.leaf 0 temp0 (by first | bool_reflect | rfl) (by bool_reflect))
    (Smap.leaf 2 temp2 (by bool_reflect) (by first | bool_reflect | rfl))

def G₁ : SimpleIrreflexiveGraph := {
  vertexSize := 3,
  edges := example_1,
  edgeSize := 3,
  edgeSizeCorrect := by rfl,
  neighborhoods := N₁,
  neighborhoodsCorrect := by rfl,
  minDegree := some 2,
  minDegreeCorrect := by rfl,
  maxDegree := some 2,
  maxDegreeCorrect := by rfl,
  isRegular := true,
  isRegularCorrect := by bool_reflect
}

-- Graph:
--  0 ------ 1
--  |        |
--  |        |
--  3 ------ 2
def example_2 : Tset Edge :=
  Stree.node (Edge.mk (0,3))
    (Stree.leaf (Edge.mk (0,1)) (by rfl) (by bool_reflect))
    (Stree.node (Edge.mk (1,2))
      (Stree.empty (by bool_reflect))
      (Stree.leaf (Edge.mk (2,3)) (by bool_reflect) (by rfl))
    )

def nbhd0 : Tset Nat :=
  Stree.node 1
    (Stree.empty (by first | bool_reflect | trivial))
    (Stree.leaf 3 (by bool_reflect) (by first | bool_reflect | trivial))

def nbhd1 : Tset Nat :=
  Stree.node 0
    (Stree.empty (by first | bool_reflect | rfl))
    (Stree.leaf 2 (by bool_reflect) (by first | bool_reflect | rfl))

def N₂ : Tmap Nat (Tset Nat) :=
  Smap.node 1 nbhd1
    (Smap.leaf 0 nbhd0 (by rfl) (by bool_reflect))
    (Smap.node 2 nbhd0
      (Smap.empty (by bool_reflect))
      (Smap.leaf 3 nbhd1 (by bool_reflect) (by rfl))
    )

def G₂ : SimpleIrreflexiveGraph := {
  vertexSize := 4,
  edges := example_2,
  edgeSize := 4,
  edgeSizeCorrect := by rfl,
  neighborhoods := N₂,
  neighborhoodsCorrect := by rfl,
  minDegree := some 2,
  minDegreeCorrect := by rfl,
  maxDegree := some 2,
  maxDegreeCorrect := by rfl,
  isRegular := true,
  isRegularCorrect := by bool_reflect
}

def partition : Tset Edge :=
  Stree.node (Edge.mk (0,1))
    (Stree.empty (by rfl))
    (Stree.leaf (Edge.mk (2,3)) (by bool_reflect) (by rfl))

def full : Tmap (Fin 4) Edge :=
  Smap.node 1 (Edge.mk (0,1))
    (Smap.leaf 0 (Edge.mk (0,1)) (by rfl) (by bool_reflect))
    (Smap.node 2 (Edge.mk (2,3))
      (Smap.empty (by bool_reflect))
      (Smap.leaf 3 (Edge.mk (2,3)) (by bool_reflect) (by rfl))
    )

instance bipartiteG₂ : Bipartite G₂ where
  partition := fun v =>
    match v with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | 3 => 1
    | _ => -1
  cond := by bool_reflect


def simpleWalk : Walk G₁ 0 1 := (Walk.trivial 0) ~- {0,1}

def exampleWalk : Walk G₁ 0 1 := Walk.right 0 0 1 (by rfl) (Walk.trivial 0)
def exampleWalk2 : Walk G₁ 0 2 := (⬝ 0) ~- {0,1} ~- {1,2}
#eval exampleWalk2

def examplePath : Path G₁ 0 2 := Path.right 0 1 2 (by rfl) exampleWalk (by bool_reflect)
def examplePath2 : Path G₁ 0 0 := (⬝ 0) ~- {0,1} ~- {1,2} ~- {2,0}

def exampleCycle : Cycle G₁ 0 := examplePath2
#eval exampleCycle
#eval exampleCycle.length


instance foop (n : Nat) : Decidable (Odd n) := by
  let x : DecidablePred Odd := fun _ => decidable_of_iff _ Nat.odd_iff.symm
  infer_instance

instance nonBipartiteG₁ : NonBipartite G₁ where
  u := 0
  cycle := exampleCycle
  isOdd := by
    let x : DecidablePred Odd := foop
    simp

end Hog