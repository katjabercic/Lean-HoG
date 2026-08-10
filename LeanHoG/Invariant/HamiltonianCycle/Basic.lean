import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

/-- A Hamiltonian cycle is a cycle which visits each vertex exactly once.

The definition of a `Cycle` already ensures that each vertex is visited at most once,
so this definition just adds that each vertex is indeed visited. -/
def Cycle.isHamiltonian {G : Graph} {u : G.vertex} (c : Cycle G u) : Bool :=
  ∀ (v : G.vertex), List.contains c.cycle.vertices v

class HamiltonianCycle (G : Graph)  where
  u : G.vertex
  cycle : Cycle G u
  isHamiltonian : cycle.isHamiltonian = true

/-- A `Graph` is Hamiltonian if it contains a Hamiltonian cycle. -/
def Graph.isHamiltonian (G : Graph) : Prop :=
  ∃ (u : G.vertex) (c : Cycle G u), c.isHamiltonian

@[simp] def Graph.isNonHamiltonian (G : Graph) : Prop := ¬ G.isHamiltonian

@[simp] def Graph.isNonHamiltonian' {G : Graph} : Prop :=
  ∀ (u : G.vertex) (c : Cycle G u), ¬c.isHamiltonian

namespace HamiltonianCycle

instance {G : Graph} : Repr (HamiltonianCycle G) where
  reprPrec p n := reprPrec p.cycle n

@[simp] theorem cycle_of_cert {G : Graph} [hc : HamiltonianCycle G] : G.isHamiltonian := by
  let ⟨u, c, cond⟩ := hc
  apply Exists.intro u
  apply Exists.intro c
  apply cond

instance {G : Graph} [HamiltonianCycle G] : Decidable (G.isHamiltonian) :=
  .isTrue cycle_of_cert

theorem equivNonHamiltonianDefs (G : Graph) :
  G.isNonHamiltonian ↔ G.isNonHamiltonian' :=
  by simp [Graph.isHamiltonian]

/-- A Hamiltonian cycle can be re-based at any vertex of `G`: since it is Hamiltonian, `v`
lies somewhere on it, so cutting the underlying closed walk where it passes through `v`
and reconnecting the two pieces in the other order gives a closed walk based at `v` with
the same vertices, hence still Hamiltonian. This is the piece `hamilton_cycle_to_sat`
needs to get from an arbitrary `HamiltonianCycle G` to one based at vertex `0`, which is
the vertex `hamiltonianCycleCNF`'s encoding fixes as the start/end (see
`firstAndLastConstraints`). -/
theorem rebase {G : Graph} (hc : HamiltonianCycle G) (v : G.vertex) :
    ∃ (hc' : HamiltonianCycle G), hc'.u = v := by
  have hham : ∀ x, x ∈ hc.cycle.cycle.vertices := by
    have h := hc.isHamiltonian
    simp only [Cycle.isHamiltonian, ClosedWalk.vertices, decide_eq_true_eq] at h
    simpa using h
  have hcyc := hc.cycle.isCycle
  rw [ClosedWalk.isCycle_eq] at hcyc
  obtain ⟨hcycV, hcycE⟩ := Bool.and_eq_true_iff.mp hcyc
  obtain ⟨w1, w2, heq⟩ := Walk.exists_split hc.cycle.cycle (hham v)
  have hham' : ∀ x, x ∈ (w2.append w1).vertices := by
    intro x
    have hx := hham x
    simp only [ClosedWalk.vertices, heq, Walk.mem_vertices_append] at hx
    simp only [Walk.mem_vertices_append]
    tauto
  have hcyc' : ClosedWalk.isCycle (w2.append w1 : ClosedWalk G v) = true := by
    rw [ClosedWalk.isCycle_eq]
    rw [heq] at hcycV hcycE
    exact Bool.and_eq_true_iff.mpr ⟨Walk.vertices_tail_append_rotate w1 w2 hcycV,
      Walk.edges_append_rotate w1 w2 hcycE⟩
  refine ⟨⟨v, ⟨w2.append w1, hcyc'⟩, ?_⟩, rfl⟩
  simp only [Cycle.isHamiltonian, ClosedWalk.vertices, decide_eq_true_eq]
  simpa using hham'

/-- A Hamiltonian cycle's vertex list has `G.vertexSize + 1` entries: `G.vertexSize` distinct
vertices, plus the closing repeat of the base vertex. Mirrors
`HamiltonianPath.length_eq_num_vertices`; needs `1 < G.vertexSize` for the same reason
`hamiltonian_cycle_to_sat` does — at `G.vertexSize = 1` the only cycle is the trivial one,
whose vertex list has length `1`, not `2`.

The count happens on the *tail*: that is the part `isCycle` makes distinct, and Hamiltonicity
makes it exhaust `G.vertex`, so it is in bijection with `G.vertex` by
`List.Nodup.getEquivOfForallMemList` — exactly as the path version counts the whole list. -/
theorem length_eq_num_vertices {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    hc.cycle.cycle.vertices.length = G.vertexSize + 1 := by
  let l := hc.cycle.cycle.vertices
  show l.length = G.vertexSize + 1
  have tad : l.tail.all_distinct :=
    (Bool.and_eq_true_iff.mp (ClosedWalk.isCycle_eq hc.cycle.cycle ▸ hc.cycle.isCycle)).1
  have nd : l.tail.Nodup := List.all_distinct_iff_nodup.mp tad
  have hham : ∀ v : G.vertex, v ∈ l := by
    have h := hc.isHamiltonian
    simp [Cycle.isHamiltonian] at h
    simpa using h
  have hcons : l = hc.u :: l.tail := Walk.vertices_first_cons_tail
  -- The cycle is nontrivial: a one-element vertex list cannot contain two distinct vertices,
  -- and `1 < G.vertexSize` provides two.
  have htne : l.tail ≠ [] := by
    intro hnil
    have h0 := hham ⟨0, by omega⟩
    have h1 := hham ⟨1, h2⟩
    rw [hcons, hnil] at h0 h1
    simp [Fin.ext_iff] at h0 h1
    omega
  have hlen1 : l.length ≠ 1 := by
    have h : 0 < l.tail.length := List.length_pos_of_ne_nil htne
    simp only [List.length_tail] at h
    omega
  -- The base vertex reappears in the tail, as the closing repeat of the cycle.
  have hu : hc.u ∈ l.tail := by
    apply List.mem_of_getLast? (a := hc.u)
    rw [List.getLast?_tail, if_neg hlen1]
    exact Walk.vertices_getLast? hc.cycle.cycle
  have hmem : ∀ v : G.vertex, v ∈ l.tail := by
    intro v
    have hv := hham v
    rw [hcons] at hv
    rcases List.mem_cons.mp hv with h | h
    · rw [h]; exact hu
    · exact h
  have equiv := List.Nodup.getEquivOfForallMemList l.tail nd hmem
  have htl : l.tail.length = G.vertexSize := by
    apply Iff.mp Fin.equiv_iff_eq
    exact Nonempty.intro equiv
  have hl : l.length = l.tail.length + 1 := by
    rw [hcons]
    simp
  omega

open Walk ClosedWalk in
def hamiltonian_cycle_on_size_1 {G : Graph} (h1 : G.vertexSize = 1) : HamiltonianCycle G where
  u := ⟨0, Nat.lt_of_sub_eq_succ h1⟩
  cycle := {
    cycle := here ⟨0, Nat.lt_of_sub_eq_succ h1⟩
    isCycle := rfl
  }
  isHamiltonian := by
    simp [Cycle.isHamiltonian]
    intro v
    apply Graph.zero_vertex_of_size_one h1

/-- No graph on two vertices is Hamiltonian, so `hamiltonianCycleCNF`'s satisfiability at
`G.vertexSize = 2` never certifies a cycle.

A Hamiltonian cycle would visit `G.vertexSize + 1 = 3` positions, hence traverse two edges,
and `ClosedWalk.isCycle` makes those two distinct; but a two-vertex graph has at most one edge
to offer. -/
theorem no_hamiltonian_cycle_on_size_2 {G : Graph} (h2 : G.vertexSize = 2) :
    ¬ G.isHamiltonian := by
  rintro ⟨u, c, hc⟩
  have hlen := length_eq_num_vertices (by omega) ⟨u, c, hc⟩
  simp only [ClosedWalk.vertices, Walk.vertices_edges_length, h2] at hlen
  have hnd : (Walk.edges c.cycle).Nodup :=
    List.all_distinct_iff_nodup.mp (Cycle.edges_all_distinct c.isCycle)
  have hsub : Fintype.card G.edge ≤ Fintype.card G.edgeType := Fintype.card_subtype_le _
  have := hnd.length_le_card
  have := Graph.edgeType_size_at_vertexSize_2 h2
  omega

end HamiltonianCycle
end LeanHoG
