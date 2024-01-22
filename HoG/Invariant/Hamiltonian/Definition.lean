import Mathlib.Tactic.LibrarySearch
import HoG.Graph
import HoG.Walk

namespace HoG

/-- A path is Hamiltonian if it contains every vertex of a graph `g`. -/
@[simp]
def Path.isHamiltonian {g : Graph} {u v : g.vertex} (p : Path g u v) : Bool :=
  ∀ (w : g.vertex), List.contains p.walk.vertices w

/-- The class representing a Hamiltonian path of a graph `g`
    going from vertex `u` to vertex `v`.
 -/
class HamiltonianPath {g : Graph} (u v : g.vertex) where
  path : Path g u v
  isHamiltonian : path.isHamiltonian = true

namespace HamiltonianPath

instance {g : Graph} {u v : g.vertex} : Repr (HamiltonianPath u v) where
  reprPrec p n := reprPrec p.path n

instance {g : Graph} : Repr ((u v : g.vertex ) ×' HamiltonianPath u v) where
  reprPrec p n := reprPrec p.2.2.path n

@[simp]
def vertices {g : Graph} {u v : g.vertex} : HamiltonianPath u v → List g.vertex :=
  fun p => p.path.vertices

@[simp]
def vertexMultiset {g : Graph} {u v : g.vertex} : HamiltonianPath u v → Multiset g.vertex :=
  fun p => p.path.vertexMultiset

@[simp]
lemma vertexMultiset_nodup {g : Graph} {u v : g.vertex} {p : HamiltonianPath u v} :
  Multiset.Nodup p.vertexMultiset := by
  apply Iff.mp Multiset.coe_nodup
  apply Iff.mp all_distinct_nodup
  apply p.path.isPath

@[simp]
def vertexFinset {g : Graph} {u v : g.vertex} : HamiltonianPath u v → Finset g.vertex := fun p =>
  ⟨p.vertexMultiset, vertexMultiset_nodup⟩

/-- The length of a Hamiltonian path is just the length of the underlying path. -/
@[simp]
def length {g : Graph} {u v : g.vertex} : HamiltonianPath u v → Nat :=
  fun p => p.path.length

lemma lt_count_eq_one {n : Nat} : ∀ (k : Nat), k < n → List.count k (List.range n) = 1 := by
  intros k k_lt_n
  have k_in_range : k ∈ (List.range n) := by apply Iff.mpr (List.mem_range) k_lt_n
  apply List.count_eq_one_of_mem (List.nodup_range n) k_in_range

lemma mem_count_ge_one {α : Type} [DecidableEq α] (l : List α) (x : α) (h : x ∈ l) :
  List.count x l ≥ 1 := by
  have : 0 < List.count x l := by apply Iff.mpr List.count_pos_iff_mem h
  simp [Nat.lt_iff_add_one_le] at this
  exact this

example {α : Type} [DecidableEq α] (l : List α) (d : l.Nodup) : Finset.card (List.toFinset l) = l.length := by
  apply List.toFinset_card_of_nodup d

lemma helper' {n : Nat} {l : List (Fin n)} :
  ∀ (k : Fin n), k ∈ l → l.length ≥ n := by
  intros k k_in_l
  have count_k_ge_one : List.count k l ≥ 1 := mem_count_ge_one l k k_in_l
  sorry

lemma helper {n : Nat} {l : List (Fin n)} :
  l.length < n → ¬ ∀ (k : Fin n), k ∈ l := by
  intro h
  by_contra h'
  sorry

lemma list_fin_lt_n_exists_x_nin_list {n : Nat} {l : List (Fin n)} :
  l.length < n → ∃ (k : Fin n), k ∉ l := by
  intro h
  by_contra h'
  sorry

lemma length_is_num_vertices {g : Graph} {u v : g.vertex} (p : HamiltonianPath u v) :
  p.length + 1 = g.vertexSize := by
  apply Iff.mpr Nat.le_antisymm_iff
  apply And.intro
  · rw [Graph.vertexSizeCard]
    apply Path.maxPathLength
  · by_contra h
    rw [not_le] at h
    rw [HamiltonianPath.length, Path.path_length_as_vertices] at h
    rw [Graph.vertexSizeCard] at h
    sorry

end HamiltonianPath

@[simp]
def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (v : g.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (g : Graph) (u : g.vertex) where
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

instance {g : Graph} {u : g.vertex} : Repr (HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex ) ×' HamiltonianCycle g u) where
  reprPrec p n := reprPrec p.2.cycle n

@[simp]
def Graph.isHamiltonian (g : Graph) : Prop :=
  ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian

class HamiltonianGraph (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

@[simp]
def Graph.isNonHamiltonian (g : Graph) : Prop := ¬ g.isHamiltonian

@[simp]
def Graph.isNonHamiltonian' {g : Graph} : Prop := ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

theorem equivNonHamiltonianDefs (g : Graph) :
  g.isNonHamiltonian ↔ g.isNonHamiltonian' :=
  by simp


end HoG
