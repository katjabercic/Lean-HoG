import Lean
import Qq
import LeanHoG.Util.Meta
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Invariant.HamiltonianPath.Correctness
import LeanHoG.Invariant.HamiltonianPath.Certificate
import LeanHoG.Invariant.HamiltonianPath.Hypotraceable
import LeanHoG.Tactic.Options
import LeanHoG.Sat.Driver

import Trestle.Encode.EncCNF

namespace LeanHoG

open Lean Elab Qq

/-- What `searchForHamiltonianPathAux` established about a graph, and how it got there.

    There is deliberately no `error` case: a solver error is reported by throwing, never
    returned. Mirrors `HamiltonicityOutcome` on the cycle side. -/
inductive TraceabilityOutcome
  /-- Traceable, certified by the path read back from the solver's assignment. -/
  | sat
  /-- Not traceable, from the LRAT-checked unsatisfiability of the encoding. -/
  | unsat
  /-- Not traceable without consulting the solver: a graph with no vertices has none to
      start a path at, and the encoding cannot answer for it. -/
  | noVertices

open Trestle Model in
/-- Decide traceability of `graph` with the SAT solver, and return the fact that
    establishes, a proof of it, and how it was established.

    A graph with no vertices is answered without running the solver, and not as an
    optimisation: `hamiltonianPathCNF` is the *empty* CNF there, which is satisfiable, so
    consulting the solver would take the SAT branch and report a Hamiltonian path in a graph
    that has no vertices to make one from. `Graph.traceable` is false at this size, by
    `no_hamiltonian_path_on_size_0`. The cycle search sets aside three sizes for the
    analogous reason — see `searchForHamiltonianCycleAux`.

    `register` says whether that fact should be backed by a declaration named after
    the *graph*: the `HamiltonianPath` instance in the SAT case, the axiom in the
    UNSAT case. The `#check_traceable` command wants one, since registering a
    reusable certificate is the whole point of the command and
    `#show_hamiltonian_path` looks the instance up by name.

    The `check_traceable` tactics must not ask for one, because a named theorem may only
    add names beneath its own prefix — see `certificateTerm`, which handles the SAT case.
    The axiom is the other half: it *has* to be a declaration, there being no other way to
    assert one, so under `register := false` it is named beneath the declaration being
    elaborated rather than after the graph. Either way an equivalent declaration already in
    the environment is reused. -/
unsafe def searchForHamiltonianPathAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × TraceabilityOutcome) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  -- The fact the two negative branches establish. Stated unfolded, as `Graph.traceable`'s
  -- definition, which is what `check_traceable`'s docstring warns about.
  let noExistsType := q(¬ ∃ (u v : Graph.vertex $graph) (p : Path $graph u v), p.isHamiltonian)
  if G.vertexSize = 0 then
    -- Not traceable, established directly rather than through the solver; see this
    -- function's docstring for why the solver must not be asked here.
    have hZeroDec : Q(decide (Graph.vertexSize $graph = 0) = true) := (q(Eq.refl true) : Lean.Expr)
    let hZero : Q(Graph.vertexSize $graph = 0) := q(of_decide_eq_true $hZeroDec)
    return (noExistsType, q(no_hamiltonian_path_on_size_0 $hZero), .noVertices)
  let enc := (hamiltonianPathCNF G).val
  let cfg ← solverConfig
  let cnf := Encode.EncCNF.toICnf enc
  let (_, s) := Encode.EncCNF.run enc
  let res ← cfg.solver.solve cnf
  match res with
  | .sat assn =>
    -- Build a Hamiltonian path from the solution given by the SAT solver
    let mut path : Array Nat := Array.replicate G.vertexSize 0
    for i in List.fins G.vertexSize do
      for j in List.fins G.vertexSize do
        match assn.findEntry? (s.vMap (Var.mk i j))  with
        | none => throwError "invalid index ({i},{j})"
        | some (_, true) => path := path.set! j i
        | some (_, false) => continue
    -- The assignment is the solver's word for it, so check that it really describes
    -- a Hamiltonian path before building a certificate out of it.
    --
    -- Soundness does not rest on this check. `hamiltonianPathOfData` proves every
    -- step by `Eq.refl` at `decide` — one adjacency, then `Walk.isPath`, then
    -- `Path.isHamiltonian` — so a bogus path cannot be accepted. But it is the
    -- *kernel* that rejects it, as an `of_decide_eq_true` type mismatch that says
    -- nothing about a solver, and the kernel check is deferred, so the command gets
    -- as far as reporting that it registered a certificate first. Checking here
    -- reports what actually went wrong, and stops before anything claims success.
    let vs := path.toList
    let solverBlame := m!"The solver named by `leanHoG.solverCmd` ({cfg.cmd}) is \
      not answering correctly."
    if vs.mergeSort (· ≤ ·) ≠ List.range G.vertexSize then
      throwError "the SAT solver returned an assignment that does not describe a \
        Hamiltonian path in {graphName}: {toString vs} is not a permutation of the \
        {G.vertexSize} vertices. {solverBlame}"
    for uv in vs.zip vs.tail do
      let (u, v) := uv
      if hu : u < G.vertexSize then
        if hv : v < G.vertexSize then
          unless G.badjacent ⟨u, hu⟩ ⟨v, hv⟩ do
            throwError "the SAT solver returned an assignment that does not describe \
              a Hamiltonian path in {graphName}: {u} and {v} are consecutive on the \
              returned path {toString vs}, but are not adjacent in the graph. \
              {solverBlame}"
    let hpQ := hamiltonianPathOfData graph ⟨path.toList⟩
    -- The certificate to hand to `path_of_cert`. The name is a function of the graph's, so
    -- a second run on the same graph — `#check_traceable G` and then the tactic, or the
    -- tactic twice — would be re-declaring it; `certificateTerm` reuses an existing
    -- `HamiltonianPath $graph` rather than failing.
    let certType : Q(Type) := q(HamiltonianPath $graph)
    let cert ← certificateTerm (certificateName graphName "HamiltonianPathI") certType
      hpQ register
    -- Applied to the certificate explicitly, not left to instance synthesis: `mkAppM`
    -- with no arguments returns the bare constant, whose implicit `G` and instance
    -- are still abstracted, and that only fails later in the kernel.
    let existsHamPath ← Meta.mkAppOptM ``LeanHoG.HamiltonianPath.path_of_cert
      #[graph, cert]
    let existsType := q(Graph.traceable $graph)
    return (existsType, existsHamPath, .sat)

  | .unsat =>
    -- The formula is UNSAT, so we assert an axiom saying so — Lean's verified LRAT checker
    -- has already accepted the solver's proof of it — and turn that into the absence of a
    -- Hamiltonian path. See `withUnsatAxiom` for where the axiom goes and why the
    -- derivation is built before it is committed.
    let type : Q(Prop) := q(((hamiltonianPathCNF $graph).val.toICnf.toStd).Unsat)
    -- The CNF is passed explicitly: the lemma is generic in the encoding, so nothing else
    -- says which one this `Unsat` is about.
    let proof ← withUnsatAxiom graphName "hamiltonianPathCNFUnsat" register type fun h => do
      let cnfExpr ← Meta.mkAppM ``LeanHoG.hamiltonianPathCNF #[graph]
      let noExistsCert ← Meta.mkAppM
        ``Trestle.Encode.VEncCNF.std_unsat_no_assignment #[cnfExpr, h]
      Meta.mkAppM ``LeanHoG.no_assignment_implies_no_hamiltonian_path' #[noExistsCert]
    return (noExistsType, proof, .unsat)

  | .error => throwError "SAT solver exited with error"


------------------------------------------
-- Find Hamiltonian path command
------------------------------------------

syntax (name := checkTraceable) "#check_traceable " ident : command
/-- `#check_traceable G` runs a SAT solver on the encoding of the Hamiltonian path problem
    on the graph `G`. It decides traceability either way:

    * **SAT.** The satisfying assignment is read back as a Hamiltonian path and registered
      as a `HamiltonianPath G` instance, which `#show_hamiltonian_path G` will then print.
    * **UNSAT.** Lean's built-in verified LRAT checker checks the produced proof. If the
      checker accepts it, we add an axiom saying there is no satisfying assignment for the
      encoding.

    This is the *command* form: it reports what it found. It proves nothing about the
    current goal — see the `check_traceable` tactic for that. The two are independent: the
    tactic does not require the command to have been run on `G` first.
-/
@[command_elab checkTraceable]
unsafe def checkTraceableImpl : Command.CommandElab
  | `(#check_traceable $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, res) ← searchForHamiltonianPathAux graphName graph (register := true)
    match res with
    | .sat =>
      logInfo m!"found Hamiltonian path, registered as \
        {certificateName graphName "HamiltonianPathI"}"
    | .unsat => logInfo m!"no Hamiltonian path found after exhaustive search"
    | .noVertices =>
      logInfo m!"{graphName} has no vertices, so it has no Hamiltonian path: there is no \
        vertex to start one at"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian path tactic
------------------------------------------

open Trestle Model in
/-- Run the Hamiltonian path search on `g` and add what it establishes to the local
    context as a hypothesis named `h` — `g.traceable` if the solver found a path, the
    negated existential if it proved there is none. Shared by the `check_traceable` and
    `check_traceablea` tactics.
-/
unsafe def assertTraceabilityFact (g : Ident) (h : Name) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (type, proof, _) ← searchForHamiltonianPathAux g.getId graph (register := false)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h type proof
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

syntax (name := checkTraceableTactic) "check_traceable " ident (" with" (ppSpace colGt ident))? : tactic
/-- `check_traceable G` runs a SAT solver on the encoding of the Hamiltonian path problem
    on the graph `G` and adds what the solver decided to the local context as a hypothesis.
    It is a decider, not a refuter: it serves goals of both signs, and you do not have to
    know which way the answer goes before invoking it.

    * **SAT.** The satisfying assignment is read back as a Hamiltonian path, and the
      hypothesis is `G.traceable`. The proof is the path itself — no axiom is involved.
    * **UNSAT.** Lean's built-in verified LRAT checker checks the produced proof. If the
      checker accepts it, we add an axiom saying there is no satisfying assignment for the
      encoding, and use it together with the encoding correctness theorem to derive the
      hypothesis `¬ ∃ u v (p : Path G u v), p.isHamiltonian`.

    **This tactic adds a hypothesis; it does not close the goal.** Finish with `assumption`,
    or use `check_traceablea`, which does that for you:

    ```lean
    example : Wheel.traceable := by
      check_traceable Wheel
      assumption

    example : ¬hog_896.traceable := by
      check_traceable hog_896
      assumption
    ```

    Note the asymmetry between the two hypotheses. In the SAT case it is `G.traceable`
    on the nose; in the UNSAT case it is the *unfolded* existential rather than
    `¬ G.traceable`, which is why `assumption` — and not `exact` against the goal as
    stated — is the right finisher in general.

    `check_traceable G with h` names the hypothesis `h` instead of leaving it inaccessible:

    ```lean
    example : ¬hog_896.traceable := by
      check_traceable hog_896 with h
      exact h
    ```

    The tactic is self-contained — it does not require `#check_traceable G` to have been
    run on `G` beforehand, and does not conflict with it if it has.
-/
@[tactic checkTraceableTactic]
unsafe def checkTraceableTacticImpl : Tactic.Tactic
  | `(tactic|check_traceable $g) => assertTraceabilityFact g .anonymous
  | `(tactic|check_traceable $g with $h) => assertTraceabilityFact g h.getId
  | _ => throwUnsupportedSyntax

syntax (name := checkTraceableaTactic) "check_traceablea " ident : tactic
/-- `check_traceablea G` is `check_traceable G` followed by `assumption`, in the same spirit
    as `simpa` for `simp`: it derives the fact about Hamiltonian paths in `G` and then uses
    it to close the goal, rather than leaving it in the context. Like `check_traceable`, it
    decides traceability in both directions:

    ```lean
    example : Wheel.traceable := by
      check_traceablea Wheel

    example : ¬hog_896.traceable := by
      check_traceablea hog_896
    ```

    Use `check_traceable` when the derived fact is a step rather than the whole proof.
-/
@[tactic checkTraceableaTactic]
unsafe def checkTraceableaTacticImpl : Tactic.Tactic
  | `(tactic|check_traceablea $g) => do
    assertTraceabilityFact g .anonymous
    Tactic.withMainContext do
      Tactic.liftMetaTactic fun mvarId => do
        try
          mvarId.assumption
          return []
        catch _ =>
          throwError "check_traceablea derived a fact about Hamiltonian paths in {g}, but it \
            does not close the goal. Use `check_traceable {g} with h` to name it and finish \
            the proof by hand."

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Hypotraceability
------------------------------------------

/-- What `searchForHypotraceabilityAux` established, and why. The two negative cases are kept
apart because they are worth different messages: a graph that is itself traceable fails the
definition at the first conjunct, and there is nothing more to say, while a graph that fails at
a particular deletion is worth naming that vertex for. -/
inductive HypotraceabilityOutcome
  /-- No Hamiltonian path, but every one-vertex deletion has one. -/
  | hypotraceable
  /-- Not hypotraceable: the graph has a Hamiltonian path itself. -/
  | traceable
  /-- Not hypotraceable: neither the graph nor the deletion of this vertex has one. -/
  | deletionNotTraceable (v : Nat)

/-- Decide hypotraceability of `graph`, and return the fact that establishes, a proof of it,
and which case it fell into.

The definition is checked in the order it is written. First `graph` itself must fail to be
traceable; if the solver finds a Hamiltonian path there, that single call settles the question
and no deletion is looked at. Then each `graph.deleteVertex v` must be traceable, and the first
one that is not settles it — so a negative answer costs at most as many solver calls as it takes
to reach the witness, while a positive one costs `graph.vertexSize + 1`.

`register` is passed through to each underlying call, so under `#check_hypotraceable` every
deletion leaves its own reusable certificate, named after the deletion rather than after
`graph`. -/
unsafe def searchForHypotraceabilityAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × HypotraceabilityOutcome) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  let (_, proofG, resG) ← searchForHamiltonianPathAux graphName graph register
  match resG with
  | .sat =>
    let proof ← Meta.mkAppM ``not_hypotraceable_of_traceable #[proofG]
    return (q(¬ Graph.hypotraceable $graph), proof, .traceable)
  | .unsat | .noVertices =>
    let mut proofs : Array Expr := #[]
    -- The index plumbing is built with `Meta` rather than quoted: a `Q(…)` mentioning the
    -- loop variable's literal sends Qq looking for a compile-time value of it and fails in
    -- `reduceEval`.
    let vsize : Q(Nat) := q(Graph.vertexSize $graph)
    for i in [0:G.vertexSize] do
      let iLit := mkNatLit i
      let hLt ← Meta.mkDecideProof (← Meta.mkAppM ``LT.lt #[iLit, vsize])
      let v ← Meta.mkAppM ``Fin.mk #[iLit, hLt]
      let sub : Q(Graph) ← Meta.mkAppM ``Graph.deleteVertex #[graph, v]
      let subName : Name := .str graphName s!"deleteVertex{i}"
      let (_, proofSub, resSub) ← searchForHamiltonianPathAux subName sub register
      match resSub with
      | .sat => proofs := proofs.push proofSub
      | .unsat | .noVertices =>
        let proof ← Meta.mkAppM ``not_hypotraceable_of_deletion #[v, proofSub]
        return (q(¬ Graph.hypotraceable $graph), proof, .deletionNotTraceable i)
    let forallType : Q(Prop) :=
      q(∀ (v : Graph.vertex $graph), Graph.traceable (Graph.deleteVertex $graph v))
    let forallProof ← mkForallVertexProof forallType proofs
    let proof ← Meta.mkAppM ``hypotraceable_of_deletions #[proofG, forallProof]
    return (q(Graph.hypotraceable $graph), proof, .hypotraceable)

syntax (name := checkHypotraceable) "#check_hypotraceable " ident : command
/-- `#check_hypotraceable G` decides whether `G` is hypotraceable — has no Hamiltonian path,
    while `G - v` has one for every vertex `v` — by running the Hamiltonian path search on `G`
    and on each of its one-vertex deletions.

    It reports which of the three ways the answer came out: hypotraceable, not hypotraceable
    because `G` is traceable, or not hypotraceable because some `G - v` is not. In the last
    case the vertex is named.

    Each underlying search registers its own certificate, so the deletions are left behind as
    `G.deleteVertexᵢ.HamiltonianPathI` instances, and the UNSAT halves as axioms named after
    the graph they refute. Deciding this is `G.vertexSize + 1` solver calls in the positive
    case, fewer once the answer is settled — see `searchForHypotraceabilityAux`.

    This is the *command* form: it reports what it found and proves nothing about the current
    goal. Use the `check_hypotraceable` tactic for that.
-/
@[command_elab checkHypotraceable]
unsafe def checkHypotraceableImpl : Command.CommandElab
  | `(#check_hypotraceable $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, outcome) ← searchForHypotraceabilityAux graphName graph (register := true)
    match outcome with
    | .hypotraceable =>
      logInfo m!"{graphName} is hypotraceable: it has no Hamiltonian path, but deleting any \
        single vertex leaves a graph that has one"
    | .traceable =>
      logInfo m!"{graphName} is not hypotraceable: it has a Hamiltonian path"
    | .deletionNotTraceable v =>
      logInfo m!"{graphName} is not hypotraceable: it has no Hamiltonian path, but neither \
        does the graph left by deleting vertex {v}"

  | _ => throwUnsupportedSyntax

/-- Run the hypotraceability search on `g` and add what it establishes to the local context as
a hypothesis named `h`: `g.hypotraceable`, or `¬ g.hypotraceable`. Shared by the
`check_hypotraceable` and `check_hypotraceablea` tactics. -/
unsafe def assertHypotraceabilityFact (g : Ident) (h : Name) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (type, proof, _) ← searchForHypotraceabilityAux g.getId graph (register := false)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h type proof
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

syntax (name := checkHypotraceableTactic) "check_hypotraceable " ident (" with" (ppSpace colGt ident))? : tactic
/-- `check_hypotraceable G` decides hypotraceability of `G` with the SAT solver and adds the
    result to the local context as a hypothesis. Like `check_traceable`, it is a decider rather
    than a refuter: the hypothesis is `G.hypotraceable` or `¬ G.hypotraceable` depending on how
    the search came out, so it serves goals of both signs.

    Unlike `check_traceable`, the hypothesis is the fact as stated in both cases — nothing is
    left unfolded — so `exact` against the goal works as well as `assumption`.

    **This tactic adds a hypothesis; it does not close the goal.** Finish with `assumption`, or
    use `check_hypotraceablea`. `check_hypotraceable G with h` names the hypothesis.

    Note the asymmetry in what the proof rests on. The positive case needs `¬ G.traceable`,
    which comes from the solver, so it depends on one unsatisfiability axiom; the Hamiltonian
    paths in the deletions are actual paths and cost nothing. A negative answer that came from
    `G` being traceable depends on no axiom at all.
-/
@[tactic checkHypotraceableTactic]
unsafe def checkHypotraceableTacticImpl : Tactic.Tactic
  | `(tactic|check_hypotraceable $g) => assertHypotraceabilityFact g .anonymous
  | `(tactic|check_hypotraceable $g with $h) => assertHypotraceabilityFact g h.getId
  | _ => throwUnsupportedSyntax

syntax (name := checkHypotraceableaTactic) "check_hypotraceablea " ident : tactic
/-- `check_hypotraceablea G` is `check_hypotraceable G` followed by `assumption`, in the same
    spirit as `simpa` for `simp`:

    ```lean
    example : ¬ Petersen.hypotraceable := by
      check_hypotraceablea Petersen
    ```
-/
@[tactic checkHypotraceableaTactic]
unsafe def checkHypotraceableaTacticImpl : Tactic.Tactic
  | `(tactic|check_hypotraceablea $g) => do
    assertHypotraceabilityFact g .anonymous
    Tactic.withMainContext do
      Tactic.liftMetaTactic fun mvarId => do
        try
          mvarId.assumption
          return []
        catch _ =>
          throwError "check_hypotraceablea derived a fact about hypotraceability of {g}, but \
            it does not close the goal. Use `check_hypotraceable {g} with h` to name it and \
            finish the proof by hand."

  | _ => throwUnsupportedSyntax

end LeanHoG
