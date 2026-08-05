# Plan: `HamiltonianCycle` SAT-encoding correctness

Goal: prove `¬ Graph.isHamiltonian G` from `hamiltonianCycleCNF`'s UNSAT, so
`HamiltonianCycle/Tactic.lean`'s `.unsat` branch can return that instead of the raw
"encoding is unsatisfiable" fact it returns today. Lives in
`LeanHoG/Invariant/HamiltonianCycle/Correctness.lean`.

## Overall stages

1. ~~Rotation lemma (`HamiltonianCycle.rebase`): a Hamiltonian cycle can be re-based at
   any vertex.~~ **Done.**
2. `hamiltonian_cycle_to_sat`: a `HamiltonianCycle G` gives a satisfying `Var`-assignment
   of `hamiltonianCycleConstraints`. **In progress — see below.**
3. `std_unsat_implies_no_assignment`: bridge the raw CNF's `Unsat` to unsatisfiability of
   the `PropFun` semantics, via `VEncCNF.toICnf_equisatisfiable`. Not started.
4. `no_assignment_implies_no_hamiltonian_cycle'`: chain 2–3 into `¬ G.isHamiltonian`. Not
   started (signature stubbed).
5. Wire into `Tactic.lean`'s `.unsat` branch; drop the disclaiming TODOs. Not started.
6. Sanity check on a small known-non-Hamiltonian graph. Not started.

## Stage 1 — done

`HamiltonianCycle.rebase` (`HamiltonianCycle/Basic.lean`) is fully proved, built from
general `Walk` infrastructure added along the way:

- `Walk.append`, `Walk.vertices_append`, `Walk.edges_append`, `Walk.length_append`
- `Walk.exists_split` (split a walk at a vertex it passes through)
- `Walk.mem_vertices_append`
- `Walk.vertices_tail_append_rotate`, `Walk.edges_append_rotate`
- `ClosedWalk.isCycle_eq` (restates the `match`-based `isCycle` as a plain `&&`)

The only remaining gap in that chain is `List.all_distinct_append_comm`
(`LeanHoG/Util/List.lean`) — deliberately left `sorry`, deferred by request.

## Finding: the encoding is unsatisfiable at `G.vertexSize = 1`

`hamiltonianCycleCNF`'s `firstAndLastConstraints` forces vertex `0` into consecutive
positions `0` and `1`. `edgeConstraints` then forbids that unless `0` is adjacent to
itself — impossible, since `Graph.irreflexiveAdjacent` rules out self-loops. So the
encoding is **unconditionally UNSAT at `n = 1`**, while a 1-vertex graph is *vacuously*
Hamiltonian on the Lean side (the trivial closed walk has no edges to repeat, so it
trivially satisfies `isCycle`/`isHamiltonian`).

Consequence: `hamiltonian_cycle_to_sat` and everything built on it needs the hypothesis
`1 < G.vertexSize`, not just `0 < G.vertexSize` — done for all of stages 2/3/4's
statements already (`std_unsat_implies_no_assignment` doesn't need it, since it's purely
about the encoding, not Hamiltonicity).

**Follow-up for stage 5**, not yet done: `Tactic.lean`'s existing `if h : 0 < G.vertexSize
then ... else throwError ...` needs to become `G.vertexSize ≤ 1`-aware. `vertexSize = 0`
keeps throwing; `vertexSize = 1` should certify the trivial cycle directly rather than
ever calling the solver, since the solver would report UNSAT there for a graph that is
actually (vacuously) Hamiltonian.

## Stage 2 — plan for `hamiltonian_cycle_to_sat`

```lean
theorem hamiltonian_cycle_to_sat {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)),
      τ |> hamiltonianCycleConstraints G (by omega)
```

Mirrors `HamiltonianPath.hamiltonian_path_to_sat`, with the rebase step new and one extra
length offset (`n+1` positions vs `n`) throughout.

1. **Rebase.** `obtain ⟨hc0, hu0⟩ := hc.rebase ⟨0, h⟩` — work with `hc0`, based at vertex
   `0`, from here on.
2. **Length.** `hc0.cycle.cycle.vertices` has length `G.vertexSize + 1`. New lemma:
   `HamiltonianCycle.length_eq_num_vertices` (stubbed in `HamiltonianCycle/Basic.lean`).
3. **Build `τ`** from `l := hc0.cycle.cycle.vertices`, the same way Path does:
   `τ ⟨i,j⟩ := decide (l.get (cast j) = i)`, using stage 2's length lemma so the cast
   lines up (`Var`'s `pos : Fin (n+1)` now matches `l.length` exactly).
4. **Discharge the four constraint groups** as `have`s inside one proof (like Path does —
   these probably don't need to be separate top-level lemmas):
   - `vertexConstraints`: "each vertex at some position" and "at most one position except
     endpoints" — needs indexing lemmas analogous to Path's local `get_subst` /
     `helper'` / `cast_eq`. Plan: re-derive small versions of these under
     `HamiltonianCycle` rather than import Path's `Correctness.lean`, to avoid coupling
     the two invariants together.
   - `positionConstraints`: "each position has a vertex" (trivial, `τ` is defined via
     `l.get`) and "at most one vertex per position" (trivial, a position determines
     `l.get j` uniquely).
   - `edgeConstraints`: follows directly from the already-proved general
     `Walk.consecutive_vertices_adjacent` — no new lemma needed.
   - `firstAndLastConstraints`: needs `l.head? = some ⟨0,h⟩` (have this —
     `Walk.vertices_first_cons_tail`) and `l.getLast? = some ⟨0,h⟩` (new lemma below).

New lemma stubs currently in the codebase, building but unproved:

```lean
-- Walk.lean
lemma vertices_getLast? {G : Graph} {u v : G.vertex} (w : Walk G u v) :
    w.vertices.getLast? = some v

-- HamiltonianCycle/Basic.lean
theorem length_eq_num_vertices {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    hc.cycle.cycle.vertices.length = G.vertexSize + 1
```

Neither is proved yet. `hamiltonian_cycle_to_sat`'s actual four-constraint proof body
hasn't been started.
