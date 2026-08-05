import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.HamiltonianCycle.Basic
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding

import Trestle.Encode.VEncCNF

namespace LeanHoG

open Trestle Model PropFun

/- Namespaced for the same reason `Var` and friends are in `SatEncoding.lean`: the analogous
   `HamiltonianPath` theorems (`std_unsat_implies_no_assignment`, ...) are bare in `LeanHoG`,
   and this file's names would otherwise clash with them. -/
namespace HamiltonianCycle

/-- STUB, see the implementation plan under discussion.

Every Hamiltonian cycle in `G` gives a satisfying assignment of `hamiltonianCycleConstraints`.
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
hypothesis. See the plan for the consequence this has for `Tactic.lean` later. -/
theorem hamiltonian_cycle_to_sat {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)),
      τ |> hamiltonianCycleConstraints G (by omega) := by
  sorry

/-- STUB, see the implementation plan under discussion.

Contrapositive of `hamiltonian_cycle_to_sat`. -/
theorem no_assignment_implies_no_hamiltonian_cycle {G : Graph} (h2 : 1 < G.vertexSize) :
    (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G (by omega)) →
    ¬ ∃ (_ : HamiltonianCycle G), True := by
  intro hno hex
  obtain ⟨hc, _⟩ := hex
  exact hno (hamiltonian_cycle_to_sat h2 hc)

/-- STUB, see the implementation plan under discussion.

Bridges the raw CNF's `Unsat` (as checked by the LRAT proof) to unsatisfiability of the
abstract `PropFun` semantics, mirroring `HamiltonianPath.std_unsat_implies_no_assignment`. -/
theorem std_unsat_implies_no_assignment {G : Graph} (h : 0 < G.vertexSize) :
    ((hamiltonianCycleCNF G h).val.toICnf.toStd).Unsat →
    ¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G h := by
  sorry

/-- STUB, see the implementation plan under discussion.

The version stated in terms of `Graph.isHamiltonian`, ready to plug into
`HamiltonianCycle.Tactic`'s `.unsat` branch in place of the raw encoding-is-unsatisfiable
fact it currently returns — once `Tactic.lean` is updated to only reach for this when
`1 < G.vertexSize` (see the note on `hamiltonian_cycle_to_sat`); `G.vertexSize ≤ 1` needs
handling separately there. -/
theorem no_assignment_implies_no_hamiltonian_cycle' {G : Graph} (h2 : 1 < G.vertexSize) :
    (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G (by omega)) →
    ¬ G.isHamiltonian := by
  sorry

end HamiltonianCycle
end LeanHoG
