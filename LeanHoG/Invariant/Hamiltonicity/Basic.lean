import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

/-- A path is Hamiltonian if it contains every vertex of a graph `g`. -/
@[simp]
def Path.isHamiltonian {g : Graph} {u v : g.vertex} (p : Path g u v) : Prop :=
  ∀ (w : g.vertex), w ∈ p.walk.vertices

instance {g : Graph} {u v : g.vertex} {p : Path g u v} :
  Decidable (p.isHamiltonian) := by
  simp
  infer_instance

/-- The class representing a Hamiltonian path of a graph `g`
    going from vertex `u` to vertex `v`.
 -/
class HamiltonianPath (g : Graph) where
  u : g.vertex
  v : g.vertex
  path : Path g u v
  isHamiltonian : path.isHamiltonian := by decide
namespace HamiltonianPath

instance {g : Graph} : Repr (HamiltonianPath g) where
  reprPrec p n := reprPrec p.path n

instance {g : Graph} : ToString (HamiltonianPath g) where
  toString p := toString p.path

@[simp] def vertices {g : Graph} : HamiltonianPath g → List g.vertex :=
  fun p => p.path.vertices

@[simp] lemma vertices_all_distinct {g : Graph} {hp : HamiltonianPath g} :
  hp.vertices.all_distinct := by
  simp
  exact hp.path.isPath

@[simp] def vertexMultiset {g : Graph} : HamiltonianPath g → Multiset g.vertex :=
  fun p => p.path.vertexMultiset

@[simp] lemma vertexMultiset_nodup {g : Graph} {p : HamiltonianPath g} :
  Multiset.Nodup p.vertexMultiset := by
  apply Iff.mp Multiset.coe_nodup
  apply Iff.mp List.all_distinct_iff_nodup
  apply p.path.isPath

@[simp] def vertexFinset {g : Graph} : HamiltonianPath g → Finset g.vertex := fun p =>
  ⟨p.vertexMultiset, vertexMultiset_nodup⟩

/-- The length of a Hamiltonian path is just the length of the underlying path.
    This is not the same as the length of the path, as that is the number of
    edges of the path.
-/
@[simp] def length {g : Graph} : HamiltonianPath g → Nat :=
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

/-- The number of vertices on a Hamiltonian path is the number of vertices in the graph. -/
@[simp] lemma length_eq_num_vertices {g : Graph} {hp : HamiltonianPath g} :
  hp.vertices.length = g.vertexSize := by
  let l := hp.vertices
  let ad : l.all_distinct := by apply hp.path.isPath
  have nd : l.Nodup := by apply Iff.mp List.all_distinct_iff_nodup ad
  have equiv := List.Nodup.getEquivOfForallMemList l nd hp.isHamiltonian
  simp at equiv
  have : List.length l = g.vertexSize := by
    apply Iff.mp Fin.equiv_iff_eq
    exact Nonempty.intro equiv
  exact this

end HamiltonianPath

@[simp] def Cycle.isHamiltonian {g : Graph} {u : g.vertex} (c : Cycle g u) : Bool :=
  ∀ (v : g.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (g : Graph)  where
  u : g.vertex
  cycle : Cycle g u
  isHamiltonian : cycle.isHamiltonian = true

instance {g : Graph} : Repr (HamiltonianCycle g) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr (HamiltonianCycle g) where
  reprPrec p n := reprPrec p.2.cycle n

@[simp] def Graph.isHamiltonian (g : Graph) : Prop :=
  ∃ (u : g.vertex) (c : Cycle g u), c.isHamiltonian

@[simp] def Graph.isNonHamiltonian (g : Graph) : Prop := ¬ g.isHamiltonian

@[simp] def Graph.isNonHamiltonian' {g : Graph} : Prop :=
  ∀ (u : g.vertex) (c : Cycle g u), ¬c.isHamiltonian

theorem equivNonHamiltonianDefs (g : Graph) :
  g.isNonHamiltonian ↔ g.isNonHamiltonian' :=
  by simp

end LeanHoG
