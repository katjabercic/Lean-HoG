import LeanHoG.Graph
import LeanHoG.Walk
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Util.List

import Trestle.Encode.VEncCNF

namespace LeanHoG

open Trestle Encode Model PropFun
open Sat

/-- Every Hamiltonian path in `G` gives a satisfying assignment of
`hamiltonianPathConstraints`: read the path off as "vertex `i` sits at position `j`".

Mirrors `HamiltonianCycle.hamiltonian_cycle_to_sat`, and is shorter than it in two ways.
There is no rotation step, the path encoding fixing no vertex; and the at-most-one-position
constraint holds of every position rather than all but the endpoints, so distinctness of the
whole vertex list settles it where the cycle needs distinctness of the tail. -/
theorem hamiltonian_path_to_sat {G : Graph} (hp : HamiltonianPath G) :
    ∃ (τ : PropAssignment (Grid.Var G.vertexSize G.vertexSize)), τ |> hamiltonianPathConstraints G := by
  let n := G.vertexSize
  let l := hp.path.walk.vertices
  have l_len : n = l.length := by
    apply Eq.symm HamiltonianPath.length_eq_num_vertices
  let τ : PropAssignment (Grid.Var G.vertexSize G.vertexSize) := fun ⟨i, j⟩ =>
    if l.get (Fin.cast l_len j) = i then true else false
  have τ_vertex : τ |> vertexConstraints G := by
    constructor
    · intro i
      obtain ⟨j, hj⟩ := List.get_of_mem (hp.isHamiltonian i)
      use (Fin.cast l_len.symm j)
      simp only [List.get_eq_getElem] at hj
      simpa [τ, hj]
    · simp
      intro i j k hjk
      by_contra
      have had : l.all_distinct := by apply hp.path.isPath
      simp [τ] at this
      have hinj := List.all_distinct_get_injective
        (h := had)
        (i := Fin.cast l_len j)
        (j := Fin.cast l_len k)
      simp [this] at hinj
      contradiction

  have τ_positions : τ |> positionConstraints G := by
    constructor
    · intro j
      set i := l[j] with h
      use i
      simpa [τ]
    · intro j i i' hne
      by_contra
      simp [τ] at this
      have : i = i' := by rw [← this.1, ← this.2]
      contradiction

  have τ_edge : τ |> edgeConstraints G := by
    simp
    intro k k' hk i i' hi
    by_contra
    simp [τ] at this
    have hadj' : G.adjacent (l.get (Fin.cast l_len k)) (l.get (Fin.cast l_len k')) := by
      apply Walk.consecutive_vertices_adjacent
      simp [hk]
    aesop

  use τ
  exact ⟨τ_vertex, τ_positions, τ_edge⟩

/-- Contrapositive of `hamiltonian_path_to_sat`. -/
theorem no_assignment_implies_no_hamiltonian_path {G : Graph} :
    (¬ ∃ (τ : PropAssignment (Grid.Var G.vertexSize G.vertexSize)), τ |> hamiltonianPathConstraints G) →
    ¬ ∃ (_ : HamiltonianPath G), True := by
  intro hno hex
  obtain ⟨hp, _⟩ := hex
  exact hno (hamiltonian_path_to_sat hp)

/-- The version stated in terms of paths rather than the `HamiltonianPath` class. This is what
`HamiltonianPath.Tactic`'s `.unsat` branch returns: composed with
`Trestle.Encode.VEncCNF.std_unsat_no_assignment`, it carries the LRAT-checked unsatisfiability
of the encoding all the way to the absence of a Hamiltonian path.

`HamiltonianPath` bundles `u`, `v`, a `Path G u v` and `isHamiltonian`, which is exactly what
the existential here provides, so this only repackages
`no_assignment_implies_no_hamiltonian_path`.

Note what it does *not* return: `¬ G.traceable`, even though `Graph.traceable` is defined as
this very existential. `no_assignment_implies_no_hamiltonian_cycle'` does fold the
corresponding step in, returning `¬ G.isHamiltonian`, and the asymmetry is why the path side
needs `Graph.no_path_not_traceable` in `find_example`'s `simp_all only [...]` set. Folding it
in here would change the fact the tactic returns, so it is a behaviour change rather than a
refactor. -/
theorem no_assignment_implies_no_hamiltonian_path' {G : Graph} :
    (¬ ∃ (τ : PropAssignment (Grid.Var G.vertexSize G.vertexSize)), τ |> hamiltonianPathConstraints G) →
    ¬ ∃ (u v : G.vertex) (p : Path G u v), p.isHamiltonian := by
  intro hno hham
  obtain ⟨u, v, p, cond⟩ := hham
  exact no_assignment_implies_no_hamiltonian_path hno
    ⟨{ u := u, v := v, path := p, isHamiltonian := cond }, trivial⟩

end LeanHoG
