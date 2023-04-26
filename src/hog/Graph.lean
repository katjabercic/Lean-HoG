import Mathlib.Data.Fintype.Sigma

import TreeSet
import TreeMap

namespace HoG

-- The endpoints of an edge must be sorted
structure Edge (vertexSize : ℕ) : Type :=
  fst : Fin vertexSize
  snd : Fin fst
  -- uncomment once https://github.com/leanprover-community/mathlib4/pull/3198 is merged
  -- deriving Fintype

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H : Nat.blt a n = true) (H2 : Nat.blt b a = true) : Edge n :=
  ⟨⟨a, by simp_all⟩, ⟨b, (by simp_all : b < a)⟩⟩

-- Get rid of this stuff once the above "deriving Fintype" works
def Graph.edgeEquiv (vertexSize : ℕ) : (fst : Fin vertexSize) × Fin fst ≃ Edge vertexSize where
  toFun z := ⟨z.1, z.2⟩
  invFun c := ⟨c.fst, c.snd⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance Edge_Fintype (vertexSize : ℕ): Fintype (Edge vertexSize) :=
  Fintype.ofEquiv _ (Graph.edgeEquiv vertexSize)

@[simp]
def nat_compare (i j : ℕ) : Ordering :=
  if i < j then .lt else (if i = j then .eq else .gt)

@[simp]
def Edge.compare {m : ℕ} (u v : Edge m) : Ordering :=
  match nat_compare u.fst v.fst with
  | .lt => .lt
  | .eq => nat_compare u.snd v.snd
  | .gt => .gt

@[simp]
instance Edge_Ord (m : ℕ): Ord (Edge m) where
  compare := Edge.compare

structure Graph : Type :=
  vertexSize : ℕ
  edgeTree : STree (Edge vertexSize)
  -- edgeCorrect : edgeTree.correct := by rfl

-- the type of graph vertices
@[simp, reducible]
def Graph.vertex (G : Graph) := Fin G.vertexSize

instance Graph_vertex_LinearOrder (G : Graph) : LinearOrder (Graph.vertex G) :=
  by simp ; infer_instance -- this seems suboptimal

-- the underlying type of edges (pairs (i,j) such that j < i < G.vertexSize)
@[simp]
def Graph.edgeType (G : Graph) := Edge G.vertexSize

instance Graph_edgeType_Finset (G : Graph) : Finset G.edgeType :=
  (Edge_Fintype G.vertexSize).elems

-- the type of edges
@[simp]
def Graph.edge (G : Graph) := { e : G.edgeType // e ∈ G.edgeTree }

instance Graph_edge_Fintype (G : Graph) : Fintype (Graph.edge G) := by
  sorry

-- the number of eges in a graph
def Graph.edgeSize (G : Graph) := Fintype.card G.edge

-- the vertex adjacency relation
@[simp]
def Graph.adjacent {G : Graph} : G.vertex → G.vertex → Bool :=
  fun u v =>
    lt_by_cases u v
      (fun u_lt_v => G.edgeTree.mem (Edge.mk v (Fin.mk u u_lt_v)))
      (fun _ => false)
      (fun v_lt_u => G.edgeTree.mem (Edge.mk u (Fin.mk v v_lt_u)))

lemma Graph.irreflexiveNeighbor (G : Graph) :
  ∀ (v : G.vertex), ¬ adjacent v v := by simp [lt_by_cases]

lemma Graph.symmetricNeighbor (G : Graph) :
  ∀ (u v : G.vertex), adjacent u v → adjacent v u := by
    intros u v
    apply lt_by_cases u v <;> (intro h ; simp [lt_by_cases, not_lt_of_lt, h])

end HoG