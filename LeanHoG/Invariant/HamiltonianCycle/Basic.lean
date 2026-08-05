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

/-- STUB, for review — see the discussion in `HamiltonianCycle/Correctness.lean`.

A Hamiltonian cycle can be re-based at any vertex of `G`: since it is Hamiltonian, `v`
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

/-- STUB, for review — see the plan for `hamiltonian_cycle_to_sat`.

A Hamiltonian cycle's vertex list has `G.vertexSize + 1` entries: `G.vertexSize` distinct
vertices, plus the closing repeat of the base vertex. Mirrors
`HamiltonianPath.length_eq_num_vertices`; needs `1 < G.vertexSize` for the same reason
`hamiltonian_cycle_to_sat` does — at `G.vertexSize = 1` the only cycle is the trivial one,
whose vertex list has length `1`, not `2`. -/
theorem length_eq_num_vertices {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    hc.cycle.cycle.vertices.length = G.vertexSize + 1 := by
  sorry

end HamiltonianCycle
end LeanHoG
