import Lean
import Graph
import TreeSet
import TreeMap
import Tactic
import ConnectedComponents
import Bipartite
import Data.Invariants

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


def G : SimpleIrreflexiveGraph := {
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

def bpG₂ : BipartiteGraph := {
  G := G₂,
  partition := partition,
  cond1 := by bool_reflect,
  full := full,
  cond2 := by bool_reflect,
  c := fun v =>
    match v with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => 0
    | _ => sorry
  cond3 := by bool_reflect
}

open Lean

def my_p : GraphInfo → Bool := fun inv => inv.vertexSize == 7

theorem thereIsAGraph : ∃ g : GraphInfo, (g.minDegree = some 2 ∧ g.isRegular = true) := by
  try_add_invariants_to_ctx
  try_find_invariant my_p
  sorry

def my_path : System.FilePath := { toString := "/home/jure/Documents/source-control/Lean-HoG"}

open Lean Lean.Elab.Tactic Expr Meta in 
elab "import_graph_for_invariant" : tactic =>
  withMainContext do
    let sysRoot ← findSysroot
    logInfo s!"{sysRoot}"
    initSearchPath my_path
    let _ ← importModules [{ module := `Data.hog00001 : Import }] {} 0
    -- let t ← (Expr.const `Hog.hog00001 [])


theorem booga : 1 = 1 := by
  import_graph_for_invariant
  let test : SimpleIrreflexiveGraph := Hog.hog00001


end Hog