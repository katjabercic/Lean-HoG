# Generalizing the SAT-encoding scaffolding

Status: **Stages 0–3 done, Stage 4 in progress** (`Sat/Grid.lean` landed, path encoding
migrated; the cycle encoding is next), Stages 5–6 not started. Mark each stage **Done** as it
lands and record what happened under `## Completed`; delete this file when the last one is, and let
it live on in history — as `PLAN.md` did (`git show 47715c3:PLAN.md`).

## Context

The last three additions to the library — the Hamiltonian cycle SAT encoding (`dae6f04`), then
hypotraceability and hypohamiltonicity (`1bc5464`) — were built by copying the Hamiltonian path
machinery and editing it. `HamiltonianCycle/SatEncoding.lean:13-18` says so in a source comment and
defers the fix; `HamiltonianCycle/Tactic.lean:341-343` labels `mkForallVertexProof` as a literal
copy of the path version.

The cost is now measurable. A new SAT encoding today means ~7 new files (900–1400 lines) plus edits
in ~10 existing files. Two symptoms show the boilerplate is already causing omissions rather than
just bloat: **no Hamiltonian certificate has ever been readable from JSON** — `loadGraphAux`
(`LeanHoG/LoadGraph.lean:50-123`) handles `canonicalForm?`, `connectedComponents?`, `twoColoring?`,
`oddClosedWalk?` and `neighborhoodMap?` but has no `hamiltonianPath?` branch at all, and
`hamiltonianCycle?` was never even added to `JSONData` — and there is no `#show_hamiltonian_cycle`
to match `#show_hamiltonian_path`.

Goal: extract the shared machinery so the next encoding is mostly its own mathematics, keeping the
hand-written `syntax` declarations and their docstrings (which are per-property and are the best
documentation in the repo).

## Guiding constraint: there is no safety net

No CI (`.github/` does not exist), no test framework. `lake build LeanHoG` type-checks and
kernel-checks everything but runs no solver; `lake build Examples` — the only integration test —
needs `cadical` **and** the network (`#download` hits houseofgraphs.org unconditionally, with no
cache check). So **Stage 0 builds the instrument** and every later stage is verified against it.

## What is being generalized

Five layers, ordered by value-per-risk (not by size):

| Layer | Removed | Risk |
|---|---|---|
| Tactic/elaborator boilerplate (5 copies of the command/tactic bodies, solver setup, axiom dance) | ~250 | ~none — elaborator only, no `Prop` touched |
| Dead code (the `tryFindHamiltonianPath` subtree, unused `Correctness` lemmas) | ~135 | none |
| One generic `std_unsat_implies_no_assignment`, shared Qq `fold`, `mkForallVertexProof` | ~30 | near-none |
| Rewrite `HamiltonianPath/Correctness.lean` in the cycle's style | ~440 | moderate, isolated to one theorem |
| Generic n×m grid CNF encoding | ~130 | moderate — **do last** |

The grid encoding is the thing the source comment flags and the obvious place to start. It is the
**last** thing to do. The fragile point is not `mapProp` and not `IndexType` (see Risks); it is the
single `aesop` at `HamiltonianPath/SatEncoding.lean:151` that bridges the legacy `Pos`
formalization to the `Var` one. Delete that bridge first and the grid work becomes routine.

---

## Stage 0 — Golden CNF fixtures (prerequisite)

New `LeanHoG/Sat/EncodingTests.lean` + `lean_lib SatEncodingTests` in `lakefile.lean` (`needs :=
\#[LeanHoG]`). Offline, solver-free, runs inside `lake build` in seconds.

Use `load_graph_from_g6` for fixtures (proven offline by `Graph6Tests.lean`). Trestle gives
`Trestle.Solver.Dimacs.formatFormula : ICnf → String` (`Dimacs.lean:31`) — the complete DIMACS text,
capturing variable numbering, clause count, clause order and literal order. Pin all three:

```lean
-- The emitted CNF must not move under refactoring. `formatFormula` is the whole DIMACS
-- text, so a changed hash means the encoding changed — regenerate only deliberately.
#guard (Encode.EncCNF.toICnf (hamiltonianPathCNF P4).val).maxVar = 16
#guard (Encode.EncCNF.toICnf (hamiltonianPathCNF P4).val).size = <from #eval>
#guard (Dimacs.formatFormula (Encode.EncCNF.toICnf (hamiltonianPathCNF P4).val)).hash = <from #eval>
```

Cover: path and cycle encodings, on a 4-vertex path, a 4-cycle, and Petersen.

When a `#guard` fires, dump both sides for a readable diff with
`Trestle.Solver.Dimacs.toFile` (`Dimacs.lean:55`) — keep that as a commented `#eval` in the file.

*Caveat:* `String.hash` is stable within a pinned toolchain, not across Lean versions. If the
toolchain moves, regenerate all three numbers in one commit.

**Verify:** `lake build SatEncodingTests` passes offline. Record `time lake build Examples` as the
baseline.

## Stage 1 — Delete dead code, fix the stray solvers

All verified unreferenced:

- **The `tryFindHamiltonianPath` subtree.** `tryFindHamiltonianPath` (`HamiltonianPath/SatEncoding.lean:252`)
  and `buildPath` (`:208`) are used only by `HamiltonianPath.toVisualizationFormat?`
  (`Widgets.lean:33`), which is called nowhere. `IO.unsafeGet` (`Widgets.lean:29`) likewise.
  Deleting these removes the reason for the two stray `instance : Trestle.Solver IO :=
  DimacsCommand "kissat"` declarations (`LoadGraph.lean:32`, `Widgets.lean:27`) — a second solver
  binary, ignoring `leanHoG.solverCmd`, with **no LRAT checking**. Delete all of it, plus the now
  unneeded `import Trestle.Solver.Impl.DimacsCommand` in both files.
- **Unused `Correctness` lemmas:** `Fin.coe` (`:12` — `@[simp, reducible]` in `namespace LeanHoG`,
  so it is live in the default simp set for no reason), `Pos.coe` (`:18`), `instance Repr (Pos n)`
  (`:21`), `hamiltonian_path_to_assignment(_expanded)` (`:379`, `:387`),
  `unsat_to_no_hamiltonian_path(_expanded)` (`:400`, `:405`), and `lemma helper`
  (`SatEncoding.lean:168`). The comment `-- unsat_to_no_hamiltonian_path` at `SatEncoding.lean:162`
  is a stale breadcrumb to a dead lemma.
- **`Download/findHamiltonianPath.py`** — line 7 is `from satEncoding import find_hamiltonian_path`
  and no `satEncoding` module exists anywhere in the repo; the script cannot run. Delete it, plus
  `HamiltonianPathEncoder` (`Download/jsonEncoder.py:23-29`) and
  `Download/Invariant/HamiltonianPath.py`, which exist only to feed it.

**Verify:** `lake build LeanHoG SatEncodingTests`. Watch for anything that was silently relying on
`Fin.coe` being in the default simp set — if a proof breaks, that is a finding worth keeping.

## Stage 2 — Pure code motion (six independent commits)

No `Prop`, no `PropPred`, no CNF is touched. Golden fixtures must stay identical throughout.

**Into `LeanHoG/Util/Meta.lean`** (18 lines today, imports only `Lean`, already hosts
`hasReusableDecl`). Also move `certificateName` here from `LoadGraph.lean:29` — every `Tactic.lean`
currently imports the whole of `LoadGraph.lean` for that one-line `Name` helper.

```lean
/-- The term to use as a certificate: the declaration `declName` if it already holds one,
    a fresh declaration under that name if `register`, and otherwise `cert` itself. -/
def certificateTerm (declName : Name) (certType cert : Expr) (register : Bool) : TermElabM Expr

/-- Assemble `∀ (v : G.vertex), P v` from one proof per vertex, in index order, as a chain
    of `Fin.cases` bottoming out at `Fin.elim0`. -/
def mkForallVertexProof (expected : Expr) (proofs : Array Expr) : TermElabM Expr

/-- Assert `type` as an axiom named after the graph and return `derive` applied to it.

    `derive` runs *first*, against a local hypothesis of `type`, so a failure while building
    the conclusion cannot leave the axiom behind on a command that then reports an error.
    `register` decides where the axiom goes: globally for a command, beneath the enclosing
    declaration for a tactic, which may not add a name outside its own prefix. -/
def withUnsatAxiom (graphName : Name) (suffix : String) (register : Bool)
    (type : Q(Prop)) (derive : Expr → TermElabM Expr) : TermElabM Expr
```

`certificateTerm` already exists, `private`, at `Bipartite/Tactic.lean:23-38`; drop `private` and
move it. `HamiltonianPath/Tactic.lean:92-109` inlines the same block, `HamiltonianCycle/Tactic.lean:42-64`
wraps it. Keep `certifyHamiltonian` where it is — it also builds the `cycle_of_cert` application and
has two call sites.

`withUnsatAxiom` is the subtlest extraction: ~35 lines, verbatim at `HamiltonianPath/Tactic.lean:118-161`
and `HamiltonianCycle/Tactic.lean:146-191`, where the *ordering* is load-bearing and documented in
only one of the two copies. Carry that comment into the docstring.

**Into `LeanHoG/Sat/Driver.lean`** (new):

```lean
/-- The LRAT-checking solver configured by `leanHoG.solverCmd`/`solverTimeout`/
    `maxCertificateSize`, with the command name for error messages. -/
def solverFromOptions : CoreM (Trestle.Solver IO × String)
```

Returning the name too is necessary: `cadicalExe` is reused in the `solverBlame` message
(`HamiltonianPath/Tactic.lean:67`, `HamiltonianCycle/Tactic.lean:122`).

**Into `LeanHoG/Util/Quote.lean`** (add `import LeanHoG.Walk`; no cycle):

```lean
/-- The walk through the given vertices, ending at `t`, as a quoted term. Every adjacency
    is `Eq.refl true` at `decide`, so the kernel rejects a list that is not a walk. -/
def walkOfVertexList (G : Q(Graph)) (t : Q(Graph.vertex $G)) :
    List Q(Graph.vertex $G) → ((s : Q(Graph.vertex $G)) ×' Q(Walk $G $s $t))
```

Replaces the `fold` in `hamiltonianPathOfData` (`HamiltonianPath/Certificate.lean:13-24`) and
`hamiltonianCycleOfData` (`HamiltonianCycle/Certificate.lean:14-25`), which differ only in a
`panic!` string. Do **not** fold in `OddClosedWalkOfData` (`Bipartite/Certificate.lean:34-44`) — it
captures the endpoint and closes the walk, so it is a near-miss, not a copy.

**Into `LeanHoG/Util/TrestleStd.lean`** (add `import Trestle.Encode.VEncCNF`):

```lean
/-- Unsatisfiability of the emitted CNF, as checked by the LRAT checker, implies
    unsatisfiability of the abstract semantics the encoding was proved against. -/
theorem VEncCNF.std_unsat_no_assignment {ν} [IndexType ν] [LawfulIndexType ν]
    {P : Model.PropPred ν} (e : Encode.VEncCNF ν Unit P)
    (h : (e.val.toICnf.toStd).Unsat) : ¬ ∃ τ, τ |> P :=
  fun hP => (ICnf.unsat_toStd_iff _).mp h ((Encode.VEncCNF.toICnf_equisatisfiable e).mpr hP)
```

Deletes both copies (`HamiltonianPath/SatEncoding.lean:180` — note it is there, not in
`Correctness.lean` — and `HamiltonianCycle/Correctness.lean:110`). Callers pass the CNF expression
they already build for the axiom's `type`; `mkAppM` recovers `ν`, `P` and the instances from it.

Also replace `imp_neg` (`Correctness.lean:377`) with core's `mt`.

**Verify after each commit:** `lake build LeanHoG`. At the end, `lake build SatEncodingTests` —
fixtures **identical**. Then, with cadical: `#check_traceable Wheel` twice in a row still reuses the
declaration rather than re-declaring, and a `check_traceable` inside a *named* `theorem` still works
(`HamiltonianPath/Tactic.lean:24-32` documents the prefix restriction that `withUnsatAxiom` now
implements).

## Stage 3 — Rewrite `HamiltonianPath/Correctness.lean` in the cycle's style — **Done**

`HamiltonianCycle/Correctness.lean` (141 lines) proves `hamiltonian_cycle_to_sat` directly against
`Var`/`PropPred`. `HamiltonianPath/Correctness.lean` (414 lines) instead builds a **second, parallel
formalization** over `def Pos (n) := Fin n × Fin n` with abbrevs `x/a/b/c/d/e`, ten
`satisfies_*_iff` lemmas, `at_least_one_at_pos`/`exactly_one`/`no_non_edges`/`has_hamiltonian_path`,
plus `SatHelpers.lean` (75 lines of `disj_list`/`conj_list`), and then transports the result to
`Var` via `posToVarAssignment`.

Replace it with:

```lean
theorem hamiltonian_path_to_sat {G : Graph} (hp : HamiltonianPath G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G
```

modelled line-for-line on `hamiltonian_cycle_to_sat` (`HamiltonianCycle/Correctness.lean:32-94`)
minus the `rebase`/`firstAndLast` parts — so ~30 lines against the cycle's 65. Every lemma it needs
already exists and is already used by the current proof: `List.all_distinct_tail_get_inj` and
friends in `Util/List.lean`, `Walk.consecutive_vertices_adjacent`,
`HamiltonianPath.length_eq_num_vertices`.

**Keep `Var`, `hamiltonianPathConstraints` and `hamiltonianPathCNF` byte-for-byte unchanged** so the
Stage 0 fixtures cannot move.

Net: ~440 lines out, ~110 in, and the two encodings become structurally symmetric — worth as much as
the line count, since the current asymmetry is itself a trap.

### The sequencing constraint that shapes this stage

The new theorem **cannot be written in `Correctness.lean` first.** `Correctness.lean` cannot see
`Var`: on the path side `SatEncoding.lean` imports `Correctness.lean`, not the other way round.
So the new proof has to be born in `SatEncoding.lean`, where both are in scope, and move to
`Correctness.lean` only once the `Pos` layer is gone and the import can be flipped. Hence three
steps rather than one, with all the proof risk isolated in the first.

### Step 3a — prove the new theorem in `SatEncoding.lean`, delete nothing — **Done**

Add, immediately below `hamiltonianPathCNF`:

```lean
theorem hamiltonian_path_to_sat {G : Graph} (hp : HamiltonianPath G) :
    ∃ (τ : PropAssignment (Var G.vertexSize)), τ |> hamiltonianPathConstraints G
```

(the old `Pos` version takes `G` explicitly; make it implicit to match the cycle). Then rewire
`hamiltonian_path_to_var_assignment` to call it, leaving the whole `Pos` chain in place but
unreferenced.

Model it on `hamiltonian_cycle_to_sat` (`HamiltonianCycle/Correctness.lean:30-94`) minus the
`rebase` and `firstAndLastConstraints` halves. Two of the three conjuncts should port almost
verbatim — `positionConstraints` is byte-identical between the two encodings, and
`edgeConstraints` differs only in the position type — and the third is *simpler* than the
cycle's, because the path's at-most-one-position constraint has no `0 < j` guard, so the two
`hj hk` hypotheses the cycle threads through disappear.

**Derisk the plumbing before the proofs.** Write the skeleton with `sorry` for each of the three
`have`s and check it elaborates first. That settles the `Fin.cast` direction (`l_len : n =
l.length`, so `Fin.cast l_len : Fin n → Fin l.length`), the field order in
`fun ⟨i, j⟩ => if l.get (Fin.cast l_len j) = i …` (`i` is the vertex, `j` the position), and
that the final `exact ⟨_, _, _⟩` matches `hamiltonianPathConstraints`' three conjuncts — none of
which is worth discovering while also debugging a proof.

Lemmas confirmed present, so nothing new has to be proved about `List` or `Walk`:

| Need | Use |
|---|---|
| every vertex is on the path | `hp.isHamiltonian`, directly — no `Bool` unfolding, unlike the cycle |
| a position for each vertex | `List.get_of_mem`, or `List.all_distinct_exists_mem` (`Util/List.lean:292`) |
| positions are distinct | `List.all_distinct_list_get_inj` (`:261`) — the whole-list analogue of the cycle's `all_distinct_tail_get_inj` |
| consecutive vertices adjacent | `Walk.consecutive_vertices_adjacent` (`Walk.lean:190`), stated for any `Walk G u v` |
| the list has `G.vertexSize` entries | `HamiltonianPath.length_eq_num_vertices` |

**Verify:** `lake build LeanHoG SatEncodingTests SolverTests`. Golden fixtures unchanged — this
step adds a `Prop` and touches no clause. `#print axioms petersen_hypohamiltonian` unchanged, and
no `sorryAx` anywhere. `set_option maxHeartbeats 400000` should not be needed by the new proof; if
it is, the rewrite is not faithful to the cycle's and is worth re-examining rather than papering
over.

This is the only step that can fail in an interesting way, and it is revertible on its own.

### Step 3b — delete the `Pos` layer — **Done**

Now unreferenced, verified by grep: `Pos`, `x`, `a`, `b`, `c`, `d`, `e`, the ten
`satisfies_*_iff` lemmas, `at_least_one_at_pos` and friends, `no_non_edges`,
`has_hamiltonian_path`, `get_subst`, `helper'`, `cast_eq`, the old `Pos`-based
`hamiltonian_path_to_sat_pos` (renamed from `hamiltonian_path_to_sat` in 3a, which handed the
clean name to the new theorem); from `SatEncoding.lean` the bridge `posToVar`, `varToPos`,
`posToVarAssignment`, `has_hamiltonian_path_to_hamiltonianPath_constraints`; and all of
`SatHelpers.lean` together with its import in `LeanHoG/Invariant/HamiltonianPath.lean:6`.

Nothing outside these three files refers to any of them — checked against `Examples.lean`,
`Graph6Tests.lean` and both test libraries. `SatHelpers.lean` carries only two `@[simp]`
attributes, both on `disj_list`/`conj_list` themselves, so removing it cannot perturb the default
simp set for unrelated goals. Deleting the file also removes the `LeanHoG.PropFun` namespace,
which several files shadow `Trestle.Model.PropFun` with; that should only reduce ambiguity, but it
is the one thing here worth a build to confirm.

**Verify:** `lake build LeanHoG SatEncodingTests SolverTests Graph6Tests`. Pure deletion, so any
breakage is a missed reference and appears as an unknown identifier.

### Step 3c — move the correctness theorems and flip the import — **Done**

Move `hamiltonian_path_to_sat`, `no_assignment_implies_no_hamiltonian_path` and
`no_assignment_implies_no_hamiltonian_path'` out of `SatEncoding.lean` into `Correctness.lean`.
Since 3b deleted that file outright, this **recreates** it, importing `SatEncoding` — which is the
inversion the stage was after, arrived at by construction rather than by editing an import line.
Re-add `import LeanHoG.Invariant.HamiltonianPath.Correctness` to
`LeanHoG/Invariant/HamiltonianPath.lean` and to `Tactic.lean`, which uses
`no_assignment_implies_no_hamiltonian_path'` and would otherwise get it transitively.

Drop `hamiltonian_path_to_var_assignment`: with the new theorem it is a one-line wrapper, and the
cycle side has no counterpart — its `no_assignment_implies_no_hamiltonian_cycle` goes straight to
the `∃ _, True` form. Mirroring that leaves both sides with the same three theorems.

**Verify:** `lake build LeanHoG SatEncodingTests SolverTests Graph6Tests`, plus `#print axioms`
unchanged. Pure code motion.

### Deliberately not in this stage

`no_assignment_implies_no_hamiltonian_path'` still returns the *unfolded* existential where the
cycle's returns `¬ G.isHamiltonian`. That asymmetry is what forces `Graph.no_path_not_traceable`
and its appearance in `find_example`'s `simp_all only [...]` set, and it is documented in
`check_traceablea`'s docstring as a user-visible wart. Changing it would alter the fact the tactic
returns, and `find_example` — which cannot be built without network access here — is one of the
callers. It is a behaviour change, not a refactor; keep it separate.

## Stage 4 — `LeanHoG/Sat/Grid.lean`

```lean
/-- `Var n m` is "row `i` occupies column `j`" of an `n × m` Boolean grid. Rows are the
    vertices of a graph; columns are positions along a walk (`m = n` for a path, `m = n+1`
    for a cycle, whose last position repeats the first).

    **The field order is load-bearing.** `EncCNF.run` derives the DIMACS numbering solely
    from the `IndexType` instance, which sends `⟨i, j⟩` to `i * m + j`. Reordering or adding
    a field renumbers every emitted CNF. -/
structure Var (n m : Nat) where
  row : Fin n
  col : Fin m
deriving DecidableEq, IndexType

abbrev VCnf (n m : Nat) := VEncCNF (Var n m) Unit
@[simp] def at' {n m} (i : Fin n) (j : Fin m) : PropFun (Var n m) := Var.mk i j
```

Atoms, each a `@[simp]` `PropPred` paired with a `VCnf` builder carrying **its own** `mapProp` —
never one `mapProp` per bundle. *(Table corrected against the file as built; see the Completed
entry for why each parameter the first draft proposed was dropped.)*

| Atom | Meaning | Path | Cycle |
|---|---|---|---|
| `rowNonempty` | every row occupies some column | ✓ | ✓ |
| `colNonempty` | every column holds some row | ✓ | ✓ |
| `rowAmoOn (p : Fin m → Prop)` | no row in two distinct columns both satisfying `p` | — | `fun j => 0 < j.val` |
| `rowAmo` | no row in two distinct columns | ✓ | — |
| `colAmo` | no column holds two distinct rows | ✓ | ✓ |
| `consecutiveRelated (R : Fin n → Fin n → Prop)` | rows in consecutive columns are `R`-related | `R := G.adjacent` | same |
| `pin (i) (j)` | row `i` fixed in column `j` | — | ×2 |

**Do not parameterize the last three further, and do not spell consecutivity as `(· + 1 = ·)`.**
`(· + 1 = ·)` on `Fin m` is *modular*, so it would relate the last column to the first — turning
the path encoding into a cycle one, which adds clauses and makes `hamiltonian_path_to_sat` false
rather than merely slow. It must be `k.val + 1 = k'.val`. The reason to keep it, `colAmo`'s `i ≠ k`,
and `pin`'s single cell concrete is the same in all three cases: the correctness proofs close
against those exact shapes (`simp [hk]` on `hk : k.val + 1 = k'.val`; `exact hik (hcon.1.symm.trans
hcon.2)` needing an `i ≠ k`; `constructor` needing a literal `∧`), and an opaque parameter leaves
those steps nothing to match.

**`rowAmo` is a second `def` reached by `mapProp`, not a `@[simp] lemma`.** The first draft proposed
`@[simp] lemma rowAmo_true : rowAmo n m (fun _ => True) = …` so the path never sees vacuous `True →`
hypotheses. Don't: its LHS competes with `@[simp] def rowAmoOn`'s own unfolding equation, whose LHS
`rowAmoOn ?n ?m ?p` also matches, and between equal-priority candidates simp's choice is
unspecified. Deriving the unconditional `rowAmo` from `rowAmoOnClauses _ _ (fun _ => True)` through
a second `mapProp` gives the path a constraint that is *syntactically* what it was before the
factoring, so nothing has to fire in the right order — and `mapProp` provably cannot change bytes.

Both encodings then become a `seq[…] |> mapProp (by aesop)` over these atoms —
`hamiltonianCycleCNF` already has that shape.

**`namespace HamiltonianCycle` does *not* go away**, as this plan claimed before Stage 3 settled
the question. Keeping the five bundle names per property — which is what keeps this stage out of the
correctness proofs — means both files still declare `Var`, `VCnf`, `vertexConstraints`,
`positionConstraints`, `edgeConstraints` and the three clause builders. The namespace stays; its
apology comment gets rewritten to say that the grid part has landed and the bundles are what remain.

**Why the `mapProp` obligations do not get harder.** Trestle's `guard` spec is
`fun τ => ∀ (h : p), P h τ` (`VEncCNF.lean:238`) — **the `Decidable` instance does not appear in
it** — and `for_all`'s is `fun τ => ∀ a ∈ arr, P a τ` (`:221`). So the goal is an equality of two
`∀`-skeletons with identical binder structure, and an opaque predicate parameter sits symmetrically
on both sides: `simp` never needs to unfold it, where today it must evaluate `0 < j.val`. The rules
that keep this true: parameterize the *guards*, never the loop nesting; one `mapProp` per atom;
keep `@[simp]` on every atom and `Array.finRange` in the simp set. These proofs are elaborated once,
generically in `G`, so none of this costs anything at tactic-invocation time.

**Acceptance test, non-negotiable: golden fixtures byte-identical.** The DIMACS index of
`Var.mk i j` is `i * m + j + 1` under both the old and new structures, because `EncCNF.run`
(`Trestle/Encode/EncCNF.lean:232`) derives `vMap` purely from `IndexType`, whose derived instance
for a two-field structure goes through the `Fin n × Fin m` proxy and `Fin.pair x y = x * m + y`.
A non-empty diff means clause emission was reordered — find out why before proceeding.

**But the hashes have two blind spots, and both need closing in this stage.**

1. **A `sorry` in a `mapProp` obligation is invisible to them.** `mapProp` is
   `fun ⟨e,he⟩ => ⟨e, h ▸ he⟩`: it touches only the `Prop` index, so a sorried obligation emits
   byte-identical clauses and every `#guard` still passes — while that index is exactly what carries
   soundness into the `.unsat` branch, via `std_unsat_no_assignment`. Close it by asserting the
   axioms rather than printing them:
   ```lean
   /-- info: 'LeanHoG.hamiltonianPathCNF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
   #guard_msgs in
   #print axioms LeanHoG.hamiltonianPathCNF
   ```
2. **Nothing is pinned below four vertices.** Two degenerate sizes are load-bearing for the tactics'
   short-circuits: the path CNF on 0 vertices is empty and therefore SAT (which is what
   `searchForHamiltonianPathAux`'s docstring rests on), and the cycle CNF on 1 vertex is
   unconditionally UNSAT (`no_assignment_implies_no_hamiltonian_cycle'`, and the `1 < G.vertexSize`
   hypothesis everywhere downstream). The 1-vertex case is UNSAT *only* because the column loop
   reaches `k = 0, k' = 1`; narrowing that loop would silently make a 1-vertex graph SAT and
   `#check_hamiltonian` would then register a certificate the kernel later rejects. `NoVertices` and
   `G1` already exist in `SolverTests.lean`.

**One thing no fixture can catch at all:** on the path side `Var n n` has both dimensions equal, so
transposing the arguments in the solver readback (`HamiltonianPath/Tactic.lean:76`) typechecks and
moves no hash. `SolverTests` is the only target that reaches it. After this stage,
`grep -rn 'Var.mk' --include=*.lean LeanHoG/` should return `Sat/Grid.lean` plus exactly the two
`Tactic.lean` readback lines — that invariant is the point of keeping `pin` in the shared file.

## Stage 5 — The search and tactic combinators

**`LeanHoG/Search/Basic.lean`:**

```lean
/-- What a search established: the fact, a proof of it, and how the answer was reached. -/
structure SearchResult (Outcome : Type) where
  fact : Q(Prop)
  proof : Expr
  outcome : Outcome

/-- A decision procedure for one graph property. `register` says whether the certificate
    should be backed by a declaration named after the graph; a tactic must pass `false`. -/
abbrev GraphSearch (Outcome : Type) := Name → Q(Graph) → Bool → TermElabM (SearchResult Outcome)

/-- Which way a search came out — all the generic combinators need to know. -/
class Polarity (Outcome : Type) where
  established : Outcome → Bool
```

A bare function type, not a type class, for the search itself: `Meta.evalExpr'` forces every search
to be `unsafe`, which does not sit in a class field; and at every call site the property is
statically known and written out, so there is nothing to infer. `Polarity` *is* a class — pure data,
no `unsafe`, three one-line instances.

Two behaviour fixes belong here. `searchForHamiltonianPathAux` currently returns
`Trestle.Solver.Res`, leaking the whole satisfying assignment to callers (which is why
`find_example` writes `match res with | .unsat => … | _ => pure ()`, `Tactic/Basic.lean:130`); give
it a real `TraceabilityOutcome`. And make it total at `vertexSize = 0` the way the cycle search
already is — today `hamiltonianPathCNF` on a 0-vertex graph is trivially SAT and
`hamiltonianPathOfData ⟨[]⟩` then `panic!`s, which `searchForHypotraceabilityAux:345-348` papers
over with a size-0 guard that then disappears. `searchForTwoColoringAux`'s bare `Bool` becomes a
two-constructor outcome, so the command's `if bipartite then … else …` names its two certificates.

**`LeanHoG/Search/Hypo.lean`** — `searchForHypotraceabilityAux` (37 lines) and
`searchForHypohamiltonicityAux` (31 lines) are the same algorithm; 26 of 31 lines are identical,
including a verbatim shared comment.

```lean
/-- The three bridging lemmas a "hypo-" property needs. See `Hypotraceable.lean`. -/
structure HypoSpec where
  property : Name        -- ``Graph.hypotraceable``
  ofDeletions : Name     -- ¬P G → (∀ v, P (G - v)) → hypo G
  notOfPositive : Name   -- P G → ¬ hypo G
  notOfDeletion : Name   -- (v) → ¬P (G - v) → ¬ hypo G

inductive HypoOutcome (Outcome : Type)
  | hypo | positive (inner : Outcome) | deletionNegative (v : Nat) (inner : Outcome)

/-- Decide `¬P G ∧ ∀ v, P (G - v)` by running `search` on `G` and, if that refutes `P`, on
    each one-vertex deletion, stopping at the first that settles the question. -/
unsafe def searchForHypoAux {Outcome} [Polarity Outcome]
    (search : GraphSearch Outcome) (spec : HypoSpec) : GraphSearch (HypoOutcome Outcome)
```

Two 4-line `HypoSpec` values replace both search functions and both outcome enums.

**`LeanHoG/Search/Tactics.lean`** — the five copies of `assertXFact` (7 lines each, identical modulo
one identifier: `HamiltonianPath/Tactic.lean:209,418`; `HamiltonianCycle/Tactic.lean:269,437`;
`Bipartite/Tactic.lean:112`) and the four copies of the `try mvarId.assumption / catch => throwError`
block:

```lean
/-- Run `search` on `g` and add the fact it establishes to the local context as `h`. -/
unsafe def assertSearchFact {Outcome} (search : GraphSearch Outcome) (g : Ident) (h : Name)
    : Tactic.TacticM Unit

/-- `assertSearchFact` then `assumption`, in the spirit of `simpa` for `simp`. `what` names
    the fact and `tac` the tactic, for the error when the goal survives. -/
unsafe def assertSearchFactAndClose {Outcome} (search : GraphSearch Outcome) (g : Ident)
    (what : MessageData) (tac : Name) : Tactic.TacticM Unit

/-- Run `search` with `register := true` and report `describe` of the outcome. -/
unsafe def reportSearch {Outcome} (search : GraphSearch Outcome)
    (describe : Name → Outcome → MessageData) (g : Ident) : Command.CommandElabM Unit
```

**The `syntax` + `@[command_elab]` + `@[tactic]` triples stay hand-written.** Each property's
`Tactic.lean` keeps four `syntax` decls, four docstrings and four one-line elaborators, plus a
`describe` function. Not generating them is deliberate: the docstrings are per-property and carry
real content (`check_traceable`'s explains the SAT/UNSAT asymmetry that `check_hamiltonian`'s
explicitly says does *not* arise there), and generating the *elaborators* is mechanically awkward —
their bodies pattern-match on the generated syntax, and a token cannot be antiquoted into a syntax
quotation, so each of four match arms per property would become hand-built `Syntax.node` +
`isOfKind` + positional `getArg`. Six uses do not amortize that. Also, `grep '"check_'` currently
finds every tactic in the repo; after a macro it would find none.

`HamiltonianCycle/Tactic.lean` should land around 220 lines, of which ~150 are docstrings.

**Also here:** `Hypotraceable.lean` and `Hypohamiltonian.lean` are the same schema at
`P := Graph.traceable` / `P := Graph.isHamiltonian`. Leave them as two files — six one-line theorems
each, and stating them concretely is what keeps the meta code on `Meta.mkAppM` and off `Expr`
surgery (`Hypotraceable.lean:11-14` says so).

**Verify:** `Examples.lean` in full. Specifically `#check_hypohamiltonian` on Petersen (positive),
Cycle7 (`.hamiltonian`) and Path3 (`.deletionNotHamiltonian`) — that set covers all three
`HypoOutcome` branches — plus `theorem petersen_hypohamiltonian` and its `#print axioms`.

## Stage 6 — The gaps the boilerplate caused

Now cheap, because Stage 2 gave us the helpers.

- **Make Hamiltonian certificates loadable from JSON.** Add `hamiltonianCycle? : Option
  HamiltonianCycleData` to `JSONData` (`LeanHoG/JsonData.lean:21`), and add the missing
  `match jsonData.hamiltonianPath?` / `hamiltonianCycle?` branches to `loadGraphAux`. Factor the
  five existing 12-line blocks (`LoadGraph.lean:65-123`) into
  `addCertificateDecl (graphName : Name) (certName : String) (certType cert : Expr) :
  CommandElabM Unit` in `Util/Meta.lean`, so each is 2 lines. Give `JSONData`'s optional fields
  `:= none` defaults so `jsonDataOfGraphData` collapses to `{ graph := data }` and adding a future
  field stops being a `LoadGraph.lean` edit. All existing `examples/*.json` stay valid — none
  carries a `hamiltonianPath` key today.
- **`#show_hamiltonian_cycle`**, mirroring `elabVisualizeHamiltonianPathCmd` (`Widgets.lean:63-82`),
  plus `HamiltonianCycle.toVisualizationFormat`. Make the payload builder take a vertex list rather
  than copying the three-key `Json.mkObj` a third time.

**Verify:** add a fixture under `examples/` carrying a `hamiltonianPath`, `load_graph` it, and
`#eval G.traceable` — it must return without a search, proving the read path is live for the first
time. Load every existing `examples/*.json` to confirm the defaults did not break parsing.

---

## Explicitly out of scope

- **The `find_example` / `SearchDSL.lean` / `ParseExpr.lean` integration tax.** Worth recording why:
  `BoolInvariant` already enumerates all 12 HoG boolean classes (including `Hypohamiltonian` and
  `Hypotraceable`) and `IntegralInvariant` 30+ (including `ChromaticNumber`), with `toId`,
  `ToString`, `boolInvariantToQuery` and the `boolean_invariant` syntax category complete against
  that list. The five edits the cycle needed were only because that one constructor was missing. For
  an invariant HoG already knows, the SearchDSL cost is **zero**. The genuinely per-encoding parts
  are `HoGEnquiry.mentionsX` (`SearchDSL.lean:347,357`), the `~q` cases in `decomposeBoolInvQ`, and
  the branch in `findExampleImpl`. If that ever becomes painful, the fix is a literal `def` table of
  `(Name × BoolInvariant × Bool)` spellings matched by head constant, not an `@[attribute]` registry
  — an attribute cannot store closures, and it would populate the table by import side effect, whose
  failure mode is silent.
- **Swapping the hand-rolled pairwise at-most-one clauses for Trestle's `Encode/Cardinality`.**
  Worth doing eventually — `amoPairwise` emits only `i < j` pairs, halving the AMO clauses — but it
  is the one change that *alters the CNF*, which would destroy the byte-identical acceptance test
  that makes every stage above cheap to verify. It also states its spec as `atMost 1 (Multiset…)`
  rather than the pairwise form both `X_to_sat` theorems prove, so it means reproving the hardest
  theorems in the repo against cardinality predicates. Separate, measured PR, after this one.
  Reject `amoCut4`/`amoOrdEncoding`/`sinzExactlyOne` outright: they use `withTemps`, changing `ν` to
  `ν ⊕ ι`, which renumbers everything and breaks the model readback.
- **Unifying `HamiltonianPathData`/`HamiltonianCycleData`.** 16 lines, and it would rename the JSON
  key `path`. Leave them.

## Risks

1. **Stage 3 is the highest-risk stage** — ~300 lines of proof deleted, ~110 written. It is isolated
   to one theorem, the cycle version is a working (and strictly harder) template, and every lemma it
   needs already exists. Ship it as its own PR.
2. **Stage 4's grid rename ripples** into the model readback (`s.vMap (Var.mk i j)`) and both
   `Correctness.lean` files. These are compile errors, not silent failures.
3. **The axiom-naming dance** (`globalName` when `register`, `enclosing ++ globalName` from a
   tactic, reuse via `hasReusableDecl` in both) must survive `withUnsatAxiom` exactly. Getting it
   wrong shows up loudly as "cannot add declaration … restricted to the prefix". Test both paths.
4. **`Examples.lean` needs the network on every run.** Consider extending the Stage 0 test library
   with offline `load_graph_from_g6` versions of the solver-backed checks, so the fast loop covers
   more than the encoding. *(Done in Stage 0 — it turned out to be a necessity, not a nicety; see
   Completed below.)*

---

## Completed

### Stage 0 — Golden CNF fixtures — **Done**

Two new test libraries, both offline, registered in `lakefile.lean`:

| Target | File | Needs | Time |
|---|---|---|---|
| `SatEncodingTests` | `LeanHoG/Sat/EncodingTests.lean` | nothing | ~11 s |
| `SolverTests` | `LeanHoG/Sat/SolverTests.lean` | `cadical` on `PATH` | ~19 s |

**`SatEncodingTests`** pins `maxVar`, clause count and the hash of
`Trestle.Solver.Dimacs.formatFormula` for both encodings on three graphs (Path3, Cycle7,
Petersen-from-graph6). Values as of this commit:

| Graph | Path encoding (`maxVar` / clauses) | Cycle encoding (`maxVar` / clauses) |
|---|---|---|
| Path3 (n=4) | 16 / 134 | 20 / 159 |
| Cycle7 (n=7) | 49 / 812 | 56 / 892 |
| Petersen (n=10) | 100 / 2450 | 110 / 2613 |

The `maxVar` column is `n * m` exactly (`m = n` for paths, `n + 1` for cycles), which is the
first direct confirmation of the numbering assumption Stage 4 rests on: `EncCNF.run` derives
the DIMACS index of `Var.mk i j` solely from `IndexType`, as `i * m + j`.

**The fixtures were negative-tested.** Reordering `seq[vertexClauses G, positionClauses G,
edgeClauses G]` to put `positionClauses` first in `hamiltonianPathCNF` still compiles — the
`mapProp (by aesop)` obligation absorbs the reassociation without complaint — and leaves
`maxVar` and clause count *unchanged*. Only the three hash guards fired. So a pure
clause-emission reordering is exactly the silent regression the plan feared, the hash is the
only one of the three checks that catches it, and it does. Perturbation reverted.

**Stage 0 also had to absorb Risk 4, because `lake build Examples` cannot run at all here.**
Three independent blockers, none caused by this work:

1. **`houseofgraphs.org` is unreachable** — HTTP 403, "blocked by default deny policy". Every
   interesting case in `Examples.lean` hangs off `#download`, so ~15 solver-backed checks and
   the capstone `traceability_not_determined_by_degree_sequence` never elaborate. On a
   sandboxed host: `sbx policy allow network houseofgraphs.org`.
2. **No `python` on `PATH`** (only `python3`), and `leanHoG.pythonExecutable` defaults to
   `"python"` — so `#download` fails before it gets as far as the network. Worth noting that
   `LeanHoG/Options.lean` registers a *second*, entirely dead option `hog.pythonExecutable`
   whose default is `"python3"`; it is imported once by `LeanHoG.lean` and read nowhere. The
   live option is `leanHoG.pythonExecutable` in `LeanHoG/Tactic/Options.lean`. Candidate for
   the Stage 1 dead-code sweep, and the defaults should probably agree.
3. **`requests` is not installed**, which `Download/downloadGraph.py` needs.

So there is no `lake build Examples` baseline to record. `SolverTests` is the substitute, and
it now covers the ground that matters for Stages 2–6 without the network:

- both traceability outcomes, and both Hamiltonicity outcomes that consult the solver;
- **all three degenerate sizes** the cycle search answers *without* the solver — `.vacuous`
  (n=1), `.twoVertices` (n=2), and `.unsat` — which is the part of `searchForHamiltonianCycleAux`
  most likely to be broken by a driver refactor;
- **all three outcomes of each hypo- search** (`Petersen` hypohamiltonian, `Cycle7`
  hamiltonian, `Path3` deletion-not-hamiltonian; `Petersen` traceable, `ThreeFour`
  deletion-not-traceable);
- the two behaviours the current code was written to protect: running `#check_traceable` twice
  on the same graph reuses the declaration, and `check_traceablea` inside a *named* `theorem`
  respects the name-prefix restriction;
- `#print axioms petersen_hypohamiltonian`, which must stay exactly
  `[propext, Classical.choice, Petersen.hamiltonianCycleCNFUnsat, Quot.sound]` — one
  unsatisfiability axiom and nothing more;
- bipartiteness, which is not SAT-backed but shares the whole command/tactic scaffolding.

- the graph on no vertices, loaded from the graph6 string `"?"`, which `examples/` has no
  fixture for.

Not covered offline: `find_example`, which inherently needs HoG.

### Path search at size 0 — **Done** (bug found by Stage 0, fixed ahead of Stage 5)

Adding the 0-vertex fixture exposed the bug Stage 5 anticipated, in a worse form than
described there. `#check_traceable` on a graph with no vertices did not merely fail:
`hamiltonianPathCNF` is the empty CNF, which is satisfiable, so the search took the SAT
branch and logged `found Hamiltonian path, registered as NoVertices.HamiltonianPathI` —
claiming a Hamiltonian path in the empty graph — before panicking in `hamiltonianPathOfData`
("no vertices") and failing with `(kernel) unknown constant '_inhabitedExprDummy'`.

Fixed, pulling the relevant part of Stage 5 forward:

- **`no_hamiltonian_path_on_size_0`** added to `HamiltonianPath/Basic.lean`: `G.vertexSize = 0
  → ¬ G.traceable`, the path analogue of `no_hamiltonian_cycle_on_size_0`.
- **`searchForHamiltonianPathAux` now returns `TraceabilityOutcome`** (`sat | unsat |
  noVertices`) instead of `Trestle.Solver.Res`, which leaked the entire satisfying assignment
  to callers and had no way to say "answered without the solver". As on the cycle side there
  is no `error` constructor: solver errors are thrown, never returned.
- **Size 0 is answered before the encoding is built**, mirroring `searchForHamiltonianCycleAux`.
  The fact is returned in the same unfolded spelling as the UNSAT branch, so the two negative
  cases behave identically under `assumption`.
- **`searchForHypotraceabilityAux`'s size-0 special case is gone.** With the underlying search
  total, the generic path reaches the same answer: the deletion loop runs zero times and the
  empty `Fin.cases` chain proves the vacuous half. `hypotraceable_on_size_zero` is kept as a
  statement of the fact, with its docstring corrected — it is no longer load-bearing.
- Call sites updated: `checkTraceableImpl` (which gained a `.noVertices` message),
  `searchForHypotraceabilityAux` (both matches), and `find_example` in `Tactic/Basic.lean`.

Verified: golden CNF fixtures unchanged (the encoding was not touched); `#check_traceable`,
`#check_hamiltonian`, `#check_hypotraceable` and `#check_hypohamiltonian` all answer on
`NoVertices`, and four `example`s confirm the facts close goals rather than merely being
produced; `#print axioms petersen_hypohamiltonian` unchanged. `find_example` could not be
exercised — it needs HoG.

**Remaining for Stage 5 on this point:** nothing for the path search. The cycle search already
short-circuits its three degenerate sizes, and `searchForTwoColoringAux` still returns a bare
`Bool`.

### Stage 1 — Dead code and the stray solvers — **Done**

234 lines deleted, 2 added, across 9 files. Everything removed was verified unreferenced first.

- **The `tryFindHamiltonianPath` subtree**, as planned: `tryFindHamiltonianPath` and `buildPath`
  from `HamiltonianPath/SatEncoding.lean`, `HamiltonianPath.toVisualizationFormat?` and
  `IO.unsafeGet` from `Widgets.lean`. With them go both stray
  `instance : Trestle.Solver IO := DimacsCommand "kissat"` declarations
  (`LoadGraph.lean`, `Widgets.lean`) and the `Trestle.Solver.Impl.DimacsCommand` imports that
  existed only for them. The library no longer names a second solver binary anywhere, and
  every path to a solver now goes through `leanHoG.solverCmd` and the LRAT checker.
- **`try_ham`, an extra find.** `load_graph`'s syntax carried an optional `(" try_ham ")?`
  that `loadGraphImpl` never matched, so `load_graph G "f" try_ham` fell through to
  `throwUnsupportedSyntax`. It was the trigger for the subtree above. Removed.
- **Unused `Correctness.lean` lemmas**, as planned: `Fin.coe`, `Pos.coe`, `Repr (Pos n)`,
  `hamiltonian_path_to_assignment(_expanded)`, `unsat_to_no_hamiltonian_path(_expanded)`, plus
  `lemma helper` and the stale `-- unsat_to_no_hamiltonian_path` breadcrumb in
  `SatEncoding.lean`. `Pos` and `imp_neg` stay — both still used until Stages 2 and 3.
- **The Python certificate path**: `Download/findHamiltonianPath.py` (which imported a
  `satEncoding` module that does not exist), `Download/Invariant/HamiltonianPath.py`, and
  `HamiltonianPathEncoder` with its import in `Download/jsonEncoder.py`.
- **`LeanHoG/Options.lean` deleted.** Its sole content was `hog.pythonExecutable`, read
  nowhere; the live option is `leanHoG.pythonExecutable` in `Tactic/Options.lean`. Setting the
  dead one silently did nothing, so removing it turns a silent no-op into an error. Its import
  is dropped from `LeanHoG.lean`.

**`Fin.coe` was the one thing worth watching and it was a non-event.** It was
`@[simp, reducible]` in `namespace LeanHoG`, hence in the default simp set for every file
importing the library; removing it broke no proof.

Verified: `lake build LeanHoG Graph6Tests SatEncodingTests SolverTests` all pass, **golden CNF
fixtures unchanged**, and `Examples` still fails at exactly its first `#download` (line 121) —
the pre-existing environment blocker — with everything before it elaborating.

### Stage 2 — Pure code motion — **Done**

Six moves plus one tidy, in six commits. No `Prop`, `PropPred` or clause was touched, and the
golden CNF fixtures were identical at every step.

| Into | What | Was |
|---|---|---|
| `Util/Meta.lean` | `mkForallVertexProof` | literal duplicate, both Hamiltonian tactic files |
| `Util/Meta.lean` | `certificateTerm`, `certificateName` | `private` in `Bipartite/Tactic.lean`, inlined on the path side, wrapped on the cycle side |
| `Sat/Driver.lean` (new) | `solverConfig`, `SolverConfig.solver` | 5 lines of option-reading, twice |
| `Certificate.lean` | `walkOfVertexList` | local `fold`, twice |
| `Util/TrestleStd.lean` | `Encode.VEncCNF.std_unsat_no_assignment` | one copy per encoding |
| `Util/Meta.lean` | `withUnsatAxiom` | ~35 lines of axiom plumbing, twice |

Also: `imp_neg` deleted in favour of core's `mt`, and `Meta.addInstance`'s priority changed from
42 to the default 1000 at all six call sites (see the separate note below).

**Two deviations from the plan, both forced.**

- **`solverFromOptions` cannot have the signature the plan gave it.** `CoreM (Solver IO × String)`
  does not typecheck: `Trestle.Solver` is a `Type 1` and `CoreM` quantifies over `Type`, so a
  solver cannot be returned from a monadic action. It is a `SolverConfig` structure plus a pure
  `SolverConfig.solver` instead. The flags `#["--no-binary", "--lrat=true"]` moved with it — they
  are what make the LRAT read-back work, so they are not a caller's parameter.
- **`walkOfVertexList` went to `LeanHoG/Certificate.lean`, not `Util/Quote.lean`.** It needs
  `Walk`, and nothing under `Util/` refers to the library's own types; `Util/Quote.lean` imports
  only `Qq`. `Certificate.lean` already builds quoted certificate data (`edgeOfData`,
  `vertexOfData`, `graphOfData`), so it belongs there.

**The `register := false` axiom-naming branch had no test, and the comment claiming to test it
was wrong.** `SolverTests.lean` said `theorem two_not_traceable` exercised the name-prefix
restriction, but `#check_traceable Two` runs earlier in the file, so the global axiom already
exists and `hasReusableDecl` short-circuits to it. The same held for every UNSAT graph in the
file: a `#check_*` command always came first. So the branch most at risk from `withUnsatAxiom`
was uncovered, and a regression would have passed the build. Closed by loading two graphs under
fresh names, never passing them to a `#check_*`, and asserting with `#print axioms` that the
axiom lands beneath the theorem —
`…two_unchecked_not_traceable.TwoUnchecked.hamiltonianPathCNFUnsat`.

**Also added to `SolverTests`:** four `#synth` checks that registered certificates are reachable
by instance synthesis, covering both registration paths (`load_graph` from JSON, and the
`#check_*` commands). Compilation alone cannot catch a priority regression — synthesis has to
actually reach the instance.

**On the instance priority.** Every `addInstance` passed 42, which entered with the first meta
code in `bd6e274` and was copied forward. It is below even `low` (100), where `default` is 1000
and `getInstances` tries higher first. Nothing depended on it — each instance is keyed on a
concrete graph and `hasReusableDecl` prevents duplicates, so there is one candidate per goal —
but `TwoColoring G` extends `VertexColoring (Fin 2) G` and `ConnectedComponentsCertificate G`
yields a `ConnectedComponents G`, so a future generic instance of either parent would have
outranked the certificate. Now 1000 everywhere.

**One incidental finding.** `import LeanHoG.Tactic` does *not* bring the bipartite commands
into scope — it pulls in the two Hamiltonian tactic modules but not
`LeanHoG.Invariant.Bipartite.Tactic`, which is reachable only via `LeanHoG.Invariant`.
`Examples.lean:7` already works around this with a separate import. Another instance of the
ad-hoc wiring this refactor is meant to tidy; not fixed here, as it is out of Stage 0's scope.

### Stage 3, Step 3a — The `Var`-level path theorem — **Done**

`hamiltonian_path_to_sat` now lives at `HamiltonianPath/SatEncoding.lean:145`, proved directly
against `Var`/`PropAssignment`, and `hamiltonian_path_to_var_assignment` closes with one `exact`
onto it. The old `Pos`-based proof was renamed `hamiltonian_path_to_sat_pos` rather than deleted,
so this step touches no other declaration and 3b stays a pure deletion.

It came out at ~50 lines against the cycle's 65, and the plan's prediction held: the
`positionConstraints` and `edgeConstraints` halves ported nearly verbatim, and the
at-most-one-position half really is simpler than the cycle's, since the path constraint has no
`0 < j` guard to thread `hj hk` through. `set_option maxHeartbeats 400000` was not needed.

The distinctness step went to `List.all_distinct_get_injective` (`Util/List.lean:73`), the version
generic in the element type, rather than `all_distinct_list_get_inj` (`:261`) as the table above
suggested. The latter is specialized to `List (Fin n)` and states injectivity in the `≠` direction;
the goal here arrives as an equality of two `get`s, so the generic one applies with no plumbing.

**What this actually buys, beyond the line count.** The live proof no longer goes through the
`aesop` at `SatEncoding.lean:209`, the `Pos`→`Var` bridge that the plan's opening section names
as the fragile point standing between here and Stage 4. It is dead code as of this commit rather
than a step in the chain from a Hamiltonian path to a satisfying assignment.

**Verified:** `lake build LeanHoG SatEncodingTests SolverTests Graph6Tests` clean, golden CNF
fixtures unmoved (this step adds a `Prop` and emits no clause), no `sorryAx`.

### Stage 3, Step 3b — The `Pos` layer deleted — **Done**

440 lines out, one line in, and every deletion was on the list the plan drew up: exactly the
`~440` predicted. `lake build LeanHoG SatEncodingTests SolverTests Graph6Tests` clean on the first
attempt, fixtures unmoved.

**`Correctness.lean` did not shrink — it went.** The plan listed its contents declaration by
declaration without noticing that the list was the *whole file*: all 365 lines, from `Pos` at `:13`
to `hamiltonian_path_to_sat_pos`, were the second formalization. There was nothing left to leave
behind, so the file is deleted here and recreated by 3c holding the `Var`-level theorems. That is
tidier than the import edit 3c originally called for: the inversion the stage wanted
(`Basic → SatEncoding → Correctness`) now happens by construction, in a new file that imports
`SatEncoding` because it always should have.

**One import had been travelling on `Correctness`'s back.** `SatEncoding.lean` uses
`List.all_distinct_get_injective` and `List.get_of_mem` but never imported `LeanHoG.Util.List`; it
was reaching them through `Correctness`. Now direct — the one line added. `Mathlib.Data.List.ProdSigma`,
which `Correctness` also pulled in, turns out to be needed by nothing that survives.

The simp-set worry came to nothing, as predicted: `SatHelpers.lean`'s two `@[simp]` attributes were
both on `disj_list`/`conj_list` themselves, and no proof anywhere was leaning on them. Dropping the
`LeanHoG.PropFun` namespace that several files shadowed `Trestle.Model.PropFun` with likewise broke
nothing.

### Stage 3, Step 3c — `Correctness.lean` recreated over `SatEncoding` — **Done**

The three theorems moved verbatim out of `SatEncoding.lean` into a new 103-line
`Correctness.lean` that imports `SatEncoding`, completing the inversion to
`Basic → SatEncoding → Correctness`. Final shape of the split, and the point of the whole stage:

| File | Before Stage 3 | After | Holds |
|---|---|---|---|
| `SatEncoding.lean` | 179 | 132 | `Var`, the three constraint families, the three clause defs, `hamiltonianPathCNF` |
| `Correctness.lean` | 365 (all `Pos`) | 103 | `hamiltonian_path_to_sat` and the two `no_assignment_implies_*` theorems |
| `SatHelpers.lean` | 75 | — | gone |

619 lines across the three files becomes 235. The stage's own deletion figure is the 440 of 3b;
the net is −384, the difference being 3a's new proof and the docstrings that came with it.

`hamiltonian_path_to_var_assignment` is gone, as planned. What made it redundant is that both
`no_assignment_*` theorems are now written in the cycle's idiom (`intro hno hex; obtain …;
exact hno (…)`), three lines each; the primed one also loses the `simp at contr` / `cases` dance
it needed while going through the wrapper.

**`Tactic.lean`'s new import is load-bearing, not tidiness.** `:133` reaches
`no_assignment_implies_no_hamiltonian_path'` through `Meta.mkAppM` on a `Name`, so the
declaration has to be in the environment; a missing import would fail at tactic-run time, not
at compile time. `SolverTests` runs cadical over both the command and the tactic branch, so
this is exercised rather than merely type-checked.

**Two redundant imports dropped from `SatEncoding.lean`.** `LeanHoG.Walk` and
`LeanHoG.Invariant.ConnectedComponents.Basic` had no uses in the file — `Walk`'s last user was
deleted in Stage 1, and `ConnectedComponents` was already dead before this work. Removing them
cannot break a downstream file relying on the transitive import, because both still arrive by a
chain the file keeps: `SatEncoding → HamiltonianPath.Basic → Walk → ConnectedComponents.Basic`.
They were duplicate edges in the import graph. `SatEncoding.lean` is now four imports.

**The same two are still on the cycle side**, at `HamiltonianCycle/SatEncoding.lean:2`, with
zero uses of `Walk.`/`ClosedWalk` in that file. Left alone here as it is outside the path-side
stage; fold it into Stage 4, which touches both encodings anyway.

**Verified:** `lake build LeanHoG SatEncodingTests SolverTests Graph6Tests` clean, fixtures
unmoved, and all three theorems depend on `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, and the same footprint the `Pos`-based chain had.

**Where this leaves Stage 4.** The `aesop` bridging `Pos` to `Var`, named in this plan's opening
section as *the* fragile point standing in the way of a shared grid encoding, no longer exists in
any form. `hamiltonianPathCNF` and `hamiltonianCycleCNF` are now the only two things that know
about their variable types, and their correctness theorems have the same shape on both sides.
