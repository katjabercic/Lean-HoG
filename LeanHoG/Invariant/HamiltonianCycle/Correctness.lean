import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.HamiltonianCycle.Basic
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding

import Trestle.Encode.VEncCNF

namespace LeanHoG

open Trestle Encode Model PropFun

/- Namespaced for the same reason `Var` and friends are in `SatEncoding.lean`: the analogous
   `HamiltonianPath` theorems (`std_unsat_implies_no_assignment`, ...) are bare in `LeanHoG`,
   and this file's names would otherwise clash with them. -/
namespace HamiltonianCycle

/-- Every Hamiltonian cycle in `G` gives a satisfying assignment of `hamiltonianCycleConstraints`.
Mirrors `HamiltonianPath.hamiltonian_path_to_sat`; the new step here is rotating the given
cycle so it starts (and ends) at vertex `0`, matching the WLOG built into
`firstAndLastConstraints`.

The hypothesis is `1 < G.vertexSize`, not just `0 < G.vertexSize`: at `G.vertexSize = 1`,
`hamiltonianCycleCNF` is unconditionally UNSAT (`firstAndLastConstraints` forces vertex `0`
into consecutive positions `0` and `1`, which `edgeConstraints` then forbids unless `0` is
adjacent to itself — impossible, since adjacency is irreflexive), while a 1-vertex graph is
*vacuously* Hamiltonian on the `HamiltonianCycle`/`Graph.isHamiltonian` side (the trivial
closed walk has no edges to repeat, so it trivially satisfies `isCycle`). So this theorem is
simply false at `G.vertexSize = 1`, and every theorem built on it inherits the same
hypothesis. See `searchForHamiltonianCycleAux` for how `Tactic.lean` avoids this size. -/
theorem hamiltonian_cycle_to_sat {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)),
      τ |> hamiltonianCycleConstraints G (by omega) := by
  let ⟨hc0, hu0⟩ := rebase hc ⟨0, Nat.zero_lt_of_lt h2⟩
  let n := G.vertexSize
  let l := hc0.cycle.cycle.vertices
  have l_len : n + 1 = l.length := by
    apply Eq.symm (length_eq_num_vertices h2 hc0)
  let τ : PropAssignment (Var G.vertexSize) := fun ⟨i, j⟩ =>
    if l.get (Fin.cast l_len j) = i then true else false
  have τ_vertex : τ |> vertexConstraints G := by
    constructor
    · intro i
      have hham : ∀ x, x ∈ l := by
        have h := hc0.isHamiltonian
        simp [Cycle.isHamiltonian] at h
        simpa using h
      obtain ⟨k, hk⟩ := List.get_of_mem (hham i)
      use (Fin.cast l_len.symm k)
      simpa [τ] using hk
    · simp
      intro i j k j_neq_k hj hk
      have hcyc_v : l.tail.all_distinct :=
        (Bool.and_eq_true_iff.mp (ClosedWalk.isCycle_eq hc0.cycle.cycle ▸ hc0.cycle.isCycle)).1
      by_contra hcon
      simp [τ] at hcon
      exact j_neq_k <| by
        simpa [Fin.ext_iff] using List.all_distinct_tail_get_inj (i := Fin.cast l_len j)
          (j := Fin.cast l_len k) hcyc_v hj hk (by simp [hcon.1, hcon.2])

  have τ_positions : τ |> positionConstraints G := by
    constructor
    · intro j
      exact ⟨l.get (Fin.cast l_len j), by simp [τ]⟩
    · intro j i k hik
      by_contra hcon
      simp [τ] at hcon
      exact hik (hcon.1.symm.trans hcon.2)

  have τ_edge : τ |> edgeConstraints G := by
    intro k k' hkk' i j hadj
    by_contra hcon
    simp [τ] at hcon
    have hadj' : G.adjacent (l.get (Fin.cast l_len k)) (l.get (Fin.cast l_len k')) :=
      Walk.consecutive_vertices_adjacent (w := hc0.cycle.cycle)
        (i := Fin.cast l_len k) (j := Fin.cast l_len k') (h := by simpa using hkk')
    exact hadj (by simpa [hcon.1, hcon.2] using hadj')

  have τ_first_last : τ |> firstAndLastConstraints G (Nat.zero_lt_of_lt h2) := by
    constructor
    · have hhead : l[0]? = some hc0.u := by
        rw [show l = hc0.u :: l.tail from Walk.vertices_first_cons_tail]
        simp
      obtain ⟨_, h0⟩ := List.getElem?_eq_some_iff.mp hhead
      simp [τ, h0, hu0]
    · have hlast : l[l.length - 1]? = some hc0.u := by
        rw [← List.getLast?_eq_getElem?]
        exact Walk.vertices_getLast? hc0.cycle.cycle
      have hn : l.length - 1 = G.vertexSize := by omega
      rw [hn] at hlast
      obtain ⟨_, hl⟩ := List.getElem?_eq_some_iff.mp hlast
      simp [τ, hl, hu0]

  use τ
  exact ⟨τ_vertex, τ_positions, τ_edge, τ_first_last⟩

/-- Contrapositive of `hamiltonian_cycle_to_sat`. -/
theorem no_assignment_implies_no_hamiltonian_cycle {G : Graph} (h2 : 1 < G.vertexSize) :
    (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G (by omega)) →
    ¬ ∃ (_ : HamiltonianCycle G), True := by
  intro hno hex
  obtain ⟨hc, _⟩ := hex
  exact hno (hamiltonian_cycle_to_sat h2 hc)

/-- Bridges the raw CNF's `Unsat` (as checked by the LRAT proof) to unsatisfiability of the
abstract `PropFun` semantics, mirroring `HamiltonianPath.std_unsat_implies_no_assignment`.

No `1 < G.vertexSize` here: this is purely about the encoding, whose clauses provably encode
`hamiltonianCycleConstraints` (that is what `hamiltonianCycleCNF`'s `VCnf` type carries). All
this does is compose the three notions of unsatisfiability. -/
theorem std_unsat_implies_no_assignment {G : Graph} (h : 0 < G.vertexSize) :
    ((hamiltonianCycleCNF G h).val.toICnf.toStd).Unsat →
    ¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G h := by
  intro hStd hConstraints
  have hICnf : ¬ Cnf.Sat (hamiltonianCycleCNF G h).val.toICnf := (ICnf.unsat_toStd_iff _).mp hStd
  apply hICnf
  exact (VEncCNF.toICnf_equisatisfiable (hamiltonianCycleCNF G h)).mpr hConstraints

/-- The version stated in terms of `Graph.isHamiltonian`, ready to plug into
`HamiltonianCycle.Tactic`'s `.unsat` branch in place of the raw encoding-is-unsatisfiable
fact it currently returns — once `Tactic.lean` is updated to only reach for this when
`1 < G.vertexSize` (see the note on `hamiltonian_cycle_to_sat`); `G.vertexSize ≤ 1` needs
handling separately there.

`Graph.isHamiltonian` unfolds to `∃ (u : G.vertex) (c : Cycle G u), c.isHamiltonian`, which is
exactly the fields of the `HamiltonianCycle` class, so this only repackages
`no_assignment_implies_no_hamiltonian_cycle`. -/
theorem no_assignment_implies_no_hamiltonian_cycle' {G : Graph} (h2 : 1 < G.vertexSize) :
    (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G (by omega)) →
    ¬ G.isHamiltonian := by
  intro hno hham
  obtain ⟨u, c, cond⟩ := hham
  exact no_assignment_implies_no_hamiltonian_cycle h2 hno
    ⟨{ u := u, cycle := c, isHamiltonian := cond }, trivial⟩

end HamiltonianCycle
end LeanHoG
