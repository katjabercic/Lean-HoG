# Plan: `HamiltonianCycle` SAT-encoding correctness

**Status: complete (2026-08-10).** Every stage below is done, including stage 7. This file has
served its purpose and is deleted in the commit that follows this one; it is kept in the history
as the record of how the development was shaped and why. Docstrings that pointed here have been
rewritten to stand on their own.

Goal: prove `¬ Graph.isHamiltonian G` from `hamiltonianCycleCNF`'s UNSAT, so
`HamiltonianCycle/Tactic.lean`'s `.unsat` branch can return that instead of the raw
"encoding is unsatisfiable" fact it returns today. Lives in
`LeanHoG/Invariant/HamiltonianCycle/Correctness.lean`.

## Overall stages

1. ~~Rotation lemma (`HamiltonianCycle.rebase`): a Hamiltonian cycle can be re-based at
   any vertex.~~ **Done.**
2. ~~`hamiltonian_cycle_to_sat`: a `HamiltonianCycle G` gives a satisfying `Var`-assignment
   of `hamiltonianCycleConstraints`.~~ **Done, and `sorryAx`-free.**
3. ~~`std_unsat_implies_no_assignment`: bridge the raw CNF's `Unsat` to unsatisfiability of
   the `PropFun` semantics, via `VEncCNF.toICnf_equisatisfiable`.~~ **Done** (four lines, as
   planned below).
4. ~~`no_assignment_implies_no_hamiltonian_cycle'`: chain 2–3 into `¬ G.isHamiltonian`.~~
   **Done** (four lines, as planned below).
5. ~~Wire into `Tactic.lean`'s `.unsat` branch; drop the disclaiming TODOs.~~ **Done** — see
   below.
6. Sanity check on a small known-non-Hamiltonian graph. **Done informally**, not committed:
   `#check_hamiltonian` on `examples/cycle3-cycle4.json` reports non-Hamiltonicity, and
   `theorem : ¬ Graph.isHamiltonian ThreeFour := by check_hamiltonian ThreeFour with h;
   exact h` goes through with `#print axioms` showing only `propext`, `Classical.choice`,
   `Quot.sound` and the LRAT-checked `ThreeFour.hamiltonianCycleCNFUnsat`. Worth turning
   into a committed example.
7. **New:** close the `G.vertexSize = 2` hole described below.

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

## Stage 2 — done

The plan that was followed, kept because it records why the proof is shaped as it is:

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
   `HamiltonianCycle.length_eq_num_vertices`, now proved in `HamiltonianCycle/Basic.lean`.
3. **Build `τ`** from `l := hc0.cycle.cycle.vertices`, the same way Path does:
   `τ ⟨i,j⟩ := decide (l.get (cast j) = i)`, using stage 2's length lemma so the cast
   lines up (`Var`'s `pos : Fin (n+1)` now matches `l.length` exactly).
4. **Discharge the four constraint groups** as `have`s inside one proof (like Path does —
   these probably don't need to be separate top-level lemmas):
   - `vertexConstraints`: "each vertex at some position" and "at most one position except
     endpoints". Path's local `get_subst` / `helper'` / `cast_eq` turned out to be
     unnecessary: the `Fin.cast` round trip `Fin.cast l_len (Fin.cast l_len.symm k)` is
     definitionally `k`. The first half is `Cycle.isHamiltonian` plus
     `List.get_of_mem` — note Path reaches surjectivity of `get` through distinctness and
     a cardinality argument, which is unavailable here (`l` repeats its head). The second
     half is `List.all_distinct_tail_get_inj`.
   - `positionConstraints`: "each position has a vertex" (trivial, `τ` is defined via
     `l.get`) and "at most one vertex per position" (trivial, a position determines
     `l.get j` uniquely).
   - `edgeConstraints`: follows directly from the already-proved general
     `Walk.consecutive_vertices_adjacent` — no new lemma needed.
   - `firstAndLastConstraints`: needs `l.head? = some ⟨0,h⟩` (have this —
     `Walk.vertices_first_cons_tail`) and `l.getLast? = some ⟨0,h⟩` (new lemma below).

Supporting lemmas this needed, all now proved:

```lean
-- Util/List.lean — distinctness of the tail is injectivity of `get` away from index 0
theorem all_distinct_tail_get_inj {α : Type} [DecidableEq α] {l : List α}
    (h : l.tail.all_distinct) {i j : Fin l.length} (hi : 0 < i.val) (hj : 0 < j.val)
    (heq : l.get i = l.get j) : i = j

-- Walk.lean — a walk's vertex list ends at its own second endpoint
lemma vertices_getLast? {G : Graph} {u v : G.vertex} (w : Walk G u v) :
    w.vertices.getLast? = some v

-- HamiltonianCycle/Basic.lean — counts the *tail*, which is the distinct, exhaustive part
theorem length_eq_num_vertices {G : Graph} (h2 : 1 < G.vertexSize) (hc : HamiltonianCycle G) :
    hc.cycle.cycle.vertices.length = G.vertexSize + 1
```

Notes from doing it, in case the encoding changes again:

- The guard on `vertexInAtMostOnePositionExceptEndpoints` is `0 < j.val ∧ 0 < k.val`, not
  the original `j.val < n ∧ k.val < n`. That matters: `isCycle` makes the vertex list's
  *tail* distinct, so positions `1 … n` are the injective range. The `< n` form would
  instead need distinctness of `dropLast`, derivable but only via `head = getLast`.
- `edgeConstraints` and `firstAndLastConstraints` go through `getElem?` rather than
  `getElem` wherever `l` gets rewritten: rewriting under `l[i]` has to transport the
  `i < l.length` side condition and `rw` fails on the motive.
- `simp` sees the `let`-bound `l` and its expansion `Walk.vertices hc0.cycle.cycle` as
  different syntax. Facts imported from `Walk` lemmas therefore need an explicit type
  ascription mentioning `l` (as in `τ_edge`'s `hadj'`), or `simp` silently fails to rewrite.

## Stage 3 — plan for `std_unsat_implies_no_assignment`

Verbatim analogue of `HamiltonianPath.std_unsat_implies_no_assignment`
(`HamiltonianPath/SatEncoding.lean:180`), which is four lines. The statement is already
stubbed in `Correctness.lean`; only the body is missing:

```lean
theorem std_unsat_implies_no_assignment {G : Graph} (h : 0 < G.vertexSize) :
    ((hamiltonianCycleCNF G h).val.toICnf.toStd).Unsat →
    ¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G h := by
  intro hStd hConstraints
  have hICnf : ¬ Cnf.Sat (hamiltonianCycleCNF G h).val.toICnf := (ICnf.unsat_toStd_iff _).mp hStd
  apply hICnf
  exact (VEncCNF.toICnf_equisatisfiable (hamiltonianCycleCNF G h)).mpr hConstraints
```

Two ingredients, both already reachable:

- `Trestle.ICnf.unsat_toStd_iff` (`LeanHoG/Util/TrestleStd.lean:96`) — imported
  transitively through `SatEncoding.lean`.
- `Trestle.Encode.VEncCNF.toICnf_equisatisfiable`
  (`.lake/packages/trestle/Trestle/Encode/VEncCNF.lean:114`).

One edit outside the proof: `Correctness.lean`'s `open Trestle Model PropFun` must become
`open Trestle Encode Model PropFun`, or `VEncCNF.toICnf_equisatisfiable` will not resolve.
Nothing else; no new import is needed.

Why it is this short: `hamiltonianCycleCNF` has type
`VCnf G.vertexSize (hamiltonianCycleConstraints G h)`, i.e. it *carries* the proof that its
clauses encode the constraints. All the semantic content was already discharged by the
`mapProp (by ext τ; simp [Clause.toPropFun, Array.finRange])` obligations in
`SatEncoding.lean`, so this stage is only plumbing between three notions of
unsatisfiability (`Std.Sat.CNF.Unsat` → `¬ Cnf.Sat` → `¬ ∃ τ, τ ⊨ P`).

This stage does **not** need `1 < G.vertexSize` — it says nothing about Hamiltonicity, only
that the encoding is satisfiable iff the constraints are. The `n = 1` gap lives entirely in
stage 2.

## Stage 4 — plan for `no_assignment_implies_no_hamiltonian_cycle'`

Also four lines, and pure repackaging — the content is
`no_assignment_implies_no_hamiltonian_cycle` (already proved, the contrapositive of stage 2):

```lean
theorem no_assignment_implies_no_hamiltonian_cycle' {G : Graph} (h2 : 1 < G.vertexSize) :
    (¬ ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianCycleConstraints G (by omega)) →
    ¬ G.isHamiltonian := by
  intro hno hham
  obtain ⟨u, c, cond⟩ := hham
  exact no_assignment_implies_no_hamiltonian_cycle h2 hno
    ⟨{ u := u, cycle := c, isHamiltonian := cond }, trivial⟩
```

`Graph.isHamiltonian` unfolds to `∃ (u : G.vertex) (c : Cycle G u), c.isHamiltonian`, which
is exactly the three fields of the `HamiltonianCycle` class, so destructuring one and
rebuilding the other is all that happens here.

Two things that could have been obstacles and are not:

- **No `Pos`/`Var` bridge.** The path development states `hamiltonian_path_to_sat` over
  `Pos n` (bare pairs) and needs `posToVarAssignment` plus
  `has_hamiltonian_path_to_hamiltonianPath_constraints` to move to `Var n`.
  `hamiltonian_cycle_to_sat` is stated over `Var G.vertexSize` and
  `hamiltonianCycleConstraints` directly, so that whole layer is unnecessary.
- **The `0 < G.vertexSize` argument does not have to be matched.** Stage 3 produces a
  statement mentioning its own hypothesis `h`; stage 4 consumes one mentioning
  `(by omega)` derived from `h2`. Definitional proof irrelevance for `Prop` makes the two
  interchangeable, so `no_assignment_implies_no_hamiltonian_cycle' h2
  (std_unsat_implies_no_assignment h ·)` typechecks without any transport.

Both bodies above have been checked against the current tree — they compile as written
(modulo the `open` change noted in stage 3).

## Stage 5 — done

`Tactic.lean`'s `.unsat` branch now returns `¬ Graph.isHamiltonian graph`, derived as
`fun hUnsat => no_assignment_implies_no_hamiltonian_cycle' h2 (std_unsat_implies_no_assignment
h hUnsat)`, built with two `Meta.mkAppM` calls exactly as the path version does at
`HamiltonianPath/Tactic.lean:169-171`. The axiom asserting the encoding's unsatisfiability is
still what the LRAT checker signs off on; it is now the *input* to a proof rather than the
output of the tactic.

What the wiring needed beyond the path version:

- **A quoted `1 < G.vertexSize`.** Both cycle theorems take it explicitly. Built the same way
  the branch already built `hQ : Q(0 < Graph.vertexSize $graph)` — `of_decide_eq_true` on a
  `decide`-reflected `Eq.refl true`, sound because the evaluated `G` already told us it
  reduces to `true`.
- **A three-way split on `G.vertexSize`.** `1 < n` goes to the solver; `n = 1` certifies
  `hamiltonian_cycle_on_size_1` directly, *never* consulting the solver (which would answer
  UNSAT for a vacuously Hamiltonian graph — see the finding above); `n = 0` still throws.
- **`Solver.Res` replaced by a `HamiltonicityOutcome` enum** (`sat` / `unsat` / `vacuous`) as
  the third component of `searchForHamiltonianCycleAux`'s result. The one-vertex case reaches
  no solver, so there is no solver answer to report there, and fabricating a `.sat ∅` would
  have misdescribed what happened. The enum also drops the `.error` case the callers had to
  match on but which never occurred (solver errors throw).
- **The certificate-registration block factored into `certifyHamiltonian`**, shared by the
  SAT and vacuous cases.

`Tactic.lean` now imports `HamiltonianCycle.Correctness`.

## Finding: the encoding is *satisfiable* at `G.vertexSize = 2`, but no such graph is Hamiltonian

Mirror image of the `n = 1` finding, and still open — see stage 7.

At two vertices the encoding is satisfiable for the graph with one edge: positions `0,1,2`
hold `0,1,0`, all interior positions distinct, both consecutive pairs adjacent. But
`ClosedWalk.isCycle` also demands *distinct edges*, and the walk `0 → 1 → 0` traverses
`{0,1}` twice. So no two-vertex graph is Hamiltonian in this library's sense, while the
encoding says otherwise.

`n = 2` is the *only* size where this happens. Write `v_j` for the vertex at position `j`;
the encoding gives distinct `v_1 … v_n` and `v_0 = v_n`. Suppose
`{v_i, v_{i+1}} = {v_j, v_{j+1}}` with `i < j`:

- `v_i = v_j` and `v_{i+1} = v_{j+1}`: with `i, j ≥ 1` distinctness forces `i = j`; with
  `i = 0` we get `v_j = v_n`, hence `j = n`, which `j ≤ n-1` excludes.
- `v_i = v_{j+1}` and `v_{i+1} = v_j`: forces `i = j+1` unless `i = 0`, and then
  `v_{j+1} = v_n` gives `j = n-1`, so `v_1 = v_{n-1}` and therefore `n = 2`.

Today this surfaces as a **kernel rejection**, not a false theorem: the tactic reports
"found Hamiltonian cycle", `hamiltonianCycleOfData` builds a certificate, and the kernel then
refuses `of_decide_eq_true (Eq.refl true)` for its `ClosedWalk.isCycle … = true` field, which
does not reduce to `true`. Loud and safe, but wrong-looking, and it predates stage 5 — the
SAT branch's assignment checks (`vs.dropLast.mergeSort`, head = last, pairwise adjacency) all
pass, since none of them looks at edge repetition.

### Decision: fix it in the tactic, not in the encoding

Two ways to close the gap were considered. **Chosen: special-case `n = 2` in `Tactic.lean`,
leaving both `hamiltonianCycleConstraints` and `ClosedWalk.isCycle` as they are.**

The rejected alternative was to add edge distinctness to the *encoding*, so that `n = 2`
becomes UNSAT and the existing `no_assignment_implies_no_hamiltonian_cycle'` (which already
accepts `1 < G.vertexSize`) answers it with no new tactic branch at all. That is genuinely
tidier at the call site, and it is why the option is worth recording rather than dismissing.
Against it:

- **It does not avoid the new theorem.** Adding a constraint group means reproving
  `hamiltonian_cycle_to_sat` for it. Take even the cheapest useful form — "no immediate
  backtrack", `v_{j-1} ≠ v_{j+1}`, O(n²) clauses and redundant for `n ≥ 3`. For `j-1 ≥ 1`
  that is `all_distinct_tail_get_inj`; for `j-1 = 0` it needs `v_0 ≠ v_2`, which tail
  distinctness gives *unless* `2 = n`. So the proof has to rule out `n = 2` from
  `hc : HamiltonianCycle G` — exactly the theorem the tactic route needs. The encoding route
  pays for that theorem *and* a clause generator, a new `mapProp` obligation, and reopening a
  finished `sorry`-free proof.
- **The cost lands at every size** to fix one degenerate one, and full edge distinctness
  (rather than the targeted form) is O(n⁴) clauses, which also inflates the LRAT proofs that
  `leanHoG.maxCertificateSize` bounds.
- **It is not a soundness fix.** At `n = 2` the encoding is *satisfiable*, so the tactic takes
  the SAT branch and the kernel rejects the certificate; nothing false is provable. The
  verified UNSAT → no-cycle direction is untouched by the gap. And the SAT direction is not
  proof-carrying either way: what guards it is the kernel checking `isCycle` by `decide` on a
  concrete certificate.

Weakening `ClosedWalk.isCycle` to drop edge distinctness — making `0 → 1 → 0` a cycle and the
encoding correct — was also rejected: it is non-standard (a cycle in a simple graph has length
≥ 3), and `isCycle` feeds `Graph.girth`, `Cycle.isTriangle`, `ShortestCycle` and `isEulerian`,
all of which would silently change meaning.

### Stage 7 — done

1. ~~A theorem that no two-vertex graph is Hamiltonian.~~ **Done** as
   `HamiltonianCycle.no_hamiltonian_cycle_on_size_2 : G.vertexSize = 2 → ¬ G.isHamiltonian`
   (`HamiltonianCycle/Basic.lean`). The counting argument is the one sketched below, but the
   contradiction is drawn numerically rather than by cases: `length_eq_num_vertices` gives three
   vertices hence two edges, `isCycle` makes them `Nodup`, and
   `2 = length ≤ Fintype.card G.edge ≤ Fintype.card G.edgeType ≤ 1` closes it by `omega`. The
   last inequality is `Graph.edgeType_size_at_vertexSize_2`, which now lives in `Graph.lean`.
2. ~~Extend `searchForHamiltonianCycleAux`'s split.~~ **Done** exactly as planned: the solver
   guard is `2 < G.vertexSize`, a new `n = 2` arm returns `¬ Graph.isHamiltonian $graph` from
   the theorem above (quoted `Graph.vertexSize $graph = 2` built by `of_decide_eq_true`, no
   solver call and no axiom), `n = 1` stays vacuous and `n = 0` still throws. The fourth
   `HamiltonicityOutcome` constructor is `twoVertices`.
3. ~~Re-run the end-to-end check on `examples/path1.json`.~~ **Done**, and extended to every
   example graph: `one.json` (vacuous), `two.json` and `path1.json` (the new `n = 2` arm, no
   axiom), `cycle7.json`, `Poussin.json`, `Hanoi2Disks.json`, `cube5.json` (SAT) and
   `cycle3-cycle4.json` (UNSAT, axiom LRAT-checked). Each was checked both as
   `#check_hamiltonian G` and as `theorem … := by check_hamiltonian G with h; exact h` with
   `#print axioms` inspected. `path1.json` no longer fails in the kernel.

Note that `two.json` changed behaviour: with no edges its encoding is genuinely UNSAT, so it
used to go through the solver and add a `hamiltonianCycleCNFUnsat` axiom. Both two-vertex graphs
are now answered on vertex count alone, so that fact became proof-carrying — at the cost of
never consulting the solver at `n = 2` even when it would agree.

Left deliberately undone: committing those checks into `Examples.lean`. The solver-backed ones
would break `lake build Examples` for anyone without `cadical` on `PATH`. Only `one.json`,
`two.json` and `path1.json` are solver-free and safe to commit unconditionally, and
`examples/one.json` plus its `load_graph G1` line are in place already.

The original sketch, kept for the record:

1. A theorem that no two-vertex graph is Hamiltonian: covering both vertices takes the single
   edge twice, so `ClosedWalk.isCycle`'s edge-distinctness half fails. Natural home is
   `HamiltonianCycle/Basic.lean`, next to `rebase` and `length_eq_num_vertices`; shape roughly
   `theorem not_isHamiltonian_of_size_2 {G : Graph} (h : G.vertexSize = 2) : ¬ G.isHamiltonian`.
   `length_eq_num_vertices` is a useful precedent for the counting, and `hamiltonian_cycle_on_size_1`
   for how the degenerate case is packaged.
2. Extend `searchForHamiltonianCycleAux`'s split to
   `2 < n` → solver, `n = 2` → not Hamiltonian (new theorem), `n = 1` → vacuously Hamiltonian,
   `n = 0` → throw. The `n = 2` arm needs a quoted `Graph.vertexSize $graph = 2` built the same
   `of_decide_eq_true` way as the existing `n = 1` arm, and a fourth `HamiltonicityOutcome`
   constructor (or reuse `.unsat` with a note — the outcome type is about *what was
   established*, and "not Hamiltonian, established without the solver" is a distinct case, so a
   new constructor is cleaner).
3. Re-run the end-to-end check on `examples/path1.json`, which is currently the reproducer: it
   should report non-Hamiltonicity instead of failing in the kernel.

Also still open from stage 6: commit the sanity check as a real example rather than leaving it
in a scratch file. `examples/cycle3-cycle4.json` (UNSAT), `examples/cycle7.json` (SAT), a
one-vertex graph (vacuous) and `examples/path1.json` (the `n = 2` case, once stage 7 lands)
would cover every branch of the tactic. Note `#check_hamiltonian` needs a solver on `PATH`
(`cadical`), which is not installed in a bare checkout.
