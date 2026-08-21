import Lean
import Qq
import LeanHoG.Util.Meta
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding
import LeanHoG.Invariant.HamiltonianCycle.Certificate
import LeanHoG.Invariant.HamiltonianCycle.Correctness
import LeanHoG.Invariant.HamiltonianCycle.Hypohamiltonian
import LeanHoG.Tactic.Options
import LeanHoG.Sat.Driver

import Trestle.Encode.EncCNF

namespace LeanHoG

open Lean Elab Qq
open HamiltonianCycle (hamiltonianCycleCNF)

/-- What `searchForHamiltonianCycleAux` established about a graph, and how it got there.

    There is deliberately no `error` case: a solver error is reported by throwing, never
    returned. -/
inductive HamiltonicityOutcome
  /-- Hamiltonian, certified by the cycle read back from the solver's assignment. -/
  | sat
  /-- Not Hamiltonian, from the LRAT-checked unsatisfiability of the encoding. -/
  | unsat
  /-- Hamiltonian without consulting the solver: a one-vertex graph is vacuously so. -/
  | vacuous
  /-- Not Hamiltonian without consulting the solver: no two-vertex graph is, even though
      the encoding is satisfiable there. -/
  | twoVertices
  /-- Not Hamiltonian without consulting the solver: a graph with no vertices has none to
      base a cycle at, and the encoding cannot even be built. -/
  | noVertices

/-- Turn a `HamiltonianCycle graph` certificate into the `graph.isHamiltonian` fact, backed
    by a declaration named after the graph when `register` says so — see `certificateTerm`.

    Called from two places: the SAT branch, and the one-vertex graph, which is vacuously
    Hamiltonian and gets its certificate without the solver. -/
private def certifyHamiltonian (graphName : Name) (graph : Q(Graph)) (register : Bool)
    (hcQ : Q(HamiltonianCycle $graph)) : TermElabM (Expr × Expr) := do
  let certType : Q(Type) := q(HamiltonianCycle $graph)
  let cert ← certificateTerm (certificateName graphName "HamiltonianCycleI") certType
    hcQ register
  let existsHamCycle ← Meta.mkAppOptM ``LeanHoG.HamiltonianCycle.cycle_of_cert
    #[graph, cert]
  return (q(Graph.isHamiltonian $graph), existsHamCycle)

open Trestle Model in
/-- Decide Hamiltonicity of `graph` with the SAT solver, and return the fact that
    establishes, a proof of it, and how it was established.

    `register` says whether that fact should be backed by a declaration named after
    the *graph*: the `HamiltonianCycle` instance when the graph is Hamiltonian, the
    axiom asserting the encoding's unsatisfiability when it is not.

    Graphs on fewer than three vertices are answered without running the solver, and not as an
    optimisation — at none of those sizes does the encoding answer for `Graph.isHamiltonian`:

    * At no vertices there is nothing to base a cycle at, so the graph is not Hamiltonian,
      and `hamiltonianCycleCNF` cannot even be built (it needs `0 < G.vertexSize`).
    * At one vertex `hamiltonianCycleCNF` is unconditionally UNSAT — `firstAndLastConstraints`
      puts vertex `0` at positions `0` and `1` both, which `edgeConstraints` then forbids,
      adjacency being irreflexive — while the graph itself is vacuously Hamiltonian. This is
      also why `no_assignment_implies_no_hamiltonian_cycle'` carries `1 < G.vertexSize`.
    * At two vertices the encoding is *satisfiable* for the graph with an edge (positions
      `0, 1, 2` holding `0, 1, 0`), but `ClosedWalk.isCycle` also demands distinct edges and
      that walk uses `{0,1}` twice, so no two-vertex graph is Hamiltonian
      (`no_hamiltonian_cycle_on_size_2`). Consulting the solver here would report SAT and then
      have the kernel reject the certificate it built.

    See `LeanHoG.Invariant.HamiltonianPath.Tactic.searchForHamiltonianPathAux` for why
    `register` must be `false` from a tactic. -/
unsafe def searchForHamiltonianCycleAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × HamiltonicityOutcome) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  if h2 : 2 < G.vertexSize then
    let h : 0 < G.vertexSize := by omega
    let enc := (hamiltonianCycleCNF G h).val
    let cfg ← solverConfig
    let cnf := Encode.EncCNF.toICnf enc
    let (_, s) := Encode.EncCNF.run enc
    let res ← cfg.solver.solve cnf
    match res with
    | .sat assn =>
      -- Build a Hamiltonian cycle from the solution given by the SAT solver.
      -- There are `G.vertexSize + 1` positions: the cycle closes up by repeating
      -- its first vertex at the last position.
      let mut cycle : Array Nat := Array.replicate (G.vertexSize + 1) 0
      for i in List.fins G.vertexSize do
        for j in List.fins (G.vertexSize + 1) do
          match assn.findEntry? (s.vMap (HamiltonianCycle.Var.mk i j)) with
          | none => throwError "invalid index ({i},{j})"
          | some (_, true) => cycle := cycle.set! j i
          | some (_, false) => continue
      -- The assignment is the solver's word for it, so check that it really describes
      -- a Hamiltonian cycle before building a certificate out of it — see the parallel
      -- check in `HamiltonianPath.Tactic.searchForHamiltonianPathAux`.
      let vs := cycle.toList
      let solverBlame := m!"The solver named by `leanHoG.solverCmd` ({cfg.cmd}) is \
        not answering correctly."
      if vs.dropLast.mergeSort (· ≤ ·) ≠ List.range G.vertexSize then
        throwError "the SAT solver returned an assignment that does not describe a \
          Hamiltonian cycle in {graphName}: {toString vs} does not have a permutation \
          of the {G.vertexSize} vertices in its first {G.vertexSize} positions. \
          {solverBlame}"
      if vs.head? ≠ vs.getLast? then
        throwError "the SAT solver returned an assignment that does not describe a \
          Hamiltonian cycle in {graphName}: {toString vs} does not start and end at \
          the same vertex. {solverBlame}"
      for uv in vs.zip vs.tail do
        let (u, v) := uv
        if hu : u < G.vertexSize then
          if hv : v < G.vertexSize then
            unless G.badjacent ⟨u, hu⟩ ⟨v, hv⟩ do
              throwError "the SAT solver returned an assignment that does not \
                describe a Hamiltonian cycle in {graphName}: {u} and {v} are \
                consecutive on the returned cycle {toString vs}, but are not \
                adjacent in the graph. {solverBlame}"
      let hcQ := hamiltonianCycleOfData graph ⟨vs⟩
      let (existsType, existsHamCycle) ← certifyHamiltonian graphName graph register hcQ
      return (existsType, existsHamCycle, .sat)

    | .unsat =>
      -- The formula is UNSAT, so we assert an axiom saying so — Lean's verified LRAT checker
      -- has already accepted the solver's proof of it — and then turn that into the graph's
      -- non-Hamiltonicity with the correctness theorems from `Correctness.lean`.
      let globalName : Name := .str graphName "hamiltonianCycleCNFUnsat"
      -- `h`/`h2` are proofs about the concrete, evaluated `G`; the returned type must instead
      -- talk about `graph`, the quoted expression the caller wrote. Reflect the same facts
      -- at that level via `decide`, which is sound here because `h`/`h2` already tell us they
      -- reduce to `true`.
      have hPos : Q(decide (0 < Graph.vertexSize $graph) = true) := (q(Eq.refl true) : Lean.Expr)
      let hQ : Q(0 < Graph.vertexSize $graph) := q(of_decide_eq_true $hPos)
      have hTwoDec : Q(decide (1 < Graph.vertexSize $graph) = true) := (q(Eq.refl true) : Lean.Expr)
      let h2Q : Q(1 < Graph.vertexSize $graph) := q(of_decide_eq_true $hTwoDec)
      let type : Q(Prop) := q(((hamiltonianCycleCNF $graph $hQ).val.toICnf.toStd).Unsat)
      let nonHamType : Q(Prop) := q(¬ Graph.isHamiltonian $graph)
      let declName : Name ←
        if (← hasReusableDecl globalName type) ∨ register then
          pure globalName
        else
          match ← Term.getDeclName? with
          | some enclosing => pure (enclosing ++ globalName)
          | none => pure globalName
      -- The CNF is passed explicitly: the lemma is generic in the encoding, so nothing else
      -- says which one this `Unsat` is about. Note the two halves disagree on which proof of
      -- `0 < G.vertexSize` appears in the assignment-free statement they share (`hQ` here,
      -- `by omega` from `h2` there); that is immaterial, as definitional proof irrelevance
      -- makes any two interchangeable.
      let derivation ← Meta.withLocalDeclD `hCnfUnsat type fun hUnsat => do
        let cnfExpr ← Meta.mkAppM
          ``LeanHoG.HamiltonianCycle.hamiltonianCycleCNF #[graph, hQ]
        let noAssignment ← Meta.mkAppM
          ``Trestle.Encode.VEncCNF.std_unsat_no_assignment #[cnfExpr, hUnsat]
        let noHamCycle ← Meta.mkAppM
          ``LeanHoG.HamiltonianCycle.no_assignment_implies_no_hamiltonian_cycle'
          #[h2Q, noAssignment]
        Meta.mkLambdaFVars #[hUnsat] (← instantiateMVars noHamCycle)
      unless ← hasReusableDecl declName type do
        let decl := Declaration.axiomDecl {
          name        := declName,
          levelParams := [],
          type        := type,
          isUnsafe    := false
        }
        trace[Elab.axiom] "{declName} : {type}"
        Term.ensureNoUnassignedMVars decl
        addDecl decl
        logWarning m!"added axiom {declName} : {type}"
      return (nonHamType, .app derivation (mkConst declName), .unsat)

    | .error => throwError "SAT solver exited with error"
  else if G.vertexSize = 2 then
    -- Not Hamiltonian, established directly rather than through the solver; see this
    -- function's docstring for why the solver must not be asked here.
    have hTwoDec : Q(decide (Graph.vertexSize $graph = 2) = true) := (q(Eq.refl true) : Lean.Expr)
    let hTwo : Q(Graph.vertexSize $graph = 2) := q(of_decide_eq_true $hTwoDec)
    return (q(¬ Graph.isHamiltonian $graph),
      q(HamiltonianCycle.no_hamiltonian_cycle_on_size_2 $hTwo), .twoVertices)
  else if G.vertexSize = 1 then
    -- Vacuously Hamiltonian, certified directly rather than through the solver; see this
    -- function's docstring for why the solver must not be asked here.
    have hOneDec : Q(decide (Graph.vertexSize $graph = 1) = true) := (q(Eq.refl true) : Lean.Expr)
    let hOne : Q(Graph.vertexSize $graph = 1) := q(of_decide_eq_true $hOneDec)
    let hcQ : Q(HamiltonianCycle $graph) :=
      q(HamiltonianCycle.hamiltonian_cycle_on_size_1 $hOne)
    let (existsType, existsHamCycle) ← certifyHamiltonian graphName graph register hcQ
    return (existsType, existsHamCycle, .vacuous)
  else
    -- No vertices left to be anything else: not Hamiltonian, for want of a vertex to base a
    -- cycle at. The encoding cannot be asked — it needs `0 < G.vertexSize` to be built at all.
    have hZeroDec : Q(decide (Graph.vertexSize $graph = 0) = true) := (q(Eq.refl true) : Lean.Expr)
    let hZero : Q(Graph.vertexSize $graph = 0) := q(of_decide_eq_true $hZeroDec)
    return (q(¬ Graph.isHamiltonian $graph),
      q(HamiltonianCycle.no_hamiltonian_cycle_on_size_0 $hZero), .noVertices)

------------------------------------------
-- Find Hamiltonian cycle command
------------------------------------------

syntax (name := checkHamiltonian) "#check_hamiltonian " ident : command
/-- `#check_hamiltonian G` runs a SAT solver on the encoding of the Hamiltonian cycle
    problem on the graph `G`. On SAT, the satisfying assignment is read back as a
    Hamiltonian cycle and registered as a `HamiltonianCycle G` instance. On UNSAT,
    Lean's built-in verified LRAT checker checks the produced proof and, if it accepts,
    an axiom asserting the encoding's unsatisfiability is added; `¬ G.isHamiltonian`
    follows from it by `HamiltonianCycle/Correctness.lean`.

    Graphs on fewer than three vertices never reach the solver: the encoding does not answer
    for `Graph.isHamiltonian` at those sizes, so they are answered directly (see
    `searchForHamiltonianCycleAux`).
-/
@[command_elab checkHamiltonian]
unsafe def checkHamiltonianImpl : Command.CommandElab
  | `(#check_hamiltonian $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, outcome) ← searchForHamiltonianCycleAux graphName graph (register := true)
    match outcome with
    | .sat =>
      logInfo m!"found Hamiltonian cycle, registered as \
        {certificateName graphName "HamiltonianCycleI"}"
    | .vacuous =>
      logInfo m!"{graphName} has a single vertex, so it is vacuously Hamiltonian; \
        registered as {certificateName graphName "HamiltonianCycleI"}"
    | .unsat =>
      logInfo m!"the encoding is unsatisfiable after exhaustive search, so {graphName} \
        has no Hamiltonian cycle"
    | .twoVertices =>
      logInfo m!"{graphName} has two vertices, so it has no Hamiltonian cycle: covering \
        both would traverse the single possible edge twice"
    | .noVertices =>
      logInfo m!"{graphName} has no vertices, so it has no Hamiltonian cycle: there is no \
        vertex to base one at"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian cycle tactic
------------------------------------------

open Trestle Model in
/-- Run the Hamiltonian cycle search on `g` and add what it establishes to the local
    context as a hypothesis named `h`: `g.isHamiltonian` when a cycle is found (or when `g`
    is a single vertex), `¬ g.isHamiltonian` when the encoding is refuted (or when `g` has
    two vertices or none). Unlike its path counterpart, this never throws for want of
    vertices — every graph gets an answer. -/
unsafe def assertHamiltonicityFact (g : Ident) (h : Name) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (type, proof, _) ← searchForHamiltonianCycleAux g.getId graph (register := false)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h type proof
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

syntax (name := checkHamiltonianTactic) "check_hamiltonian " ident (" with" (ppSpace colGt ident))? : tactic
/-- `check_hamiltonian G` is the tactic form of `#check_hamiltonian` — see its
    docstring. This tactic adds a hypothesis; it does not close the goal.

    `check_hamiltonian G with h` names the hypothesis `h` instead of leaving it
    inaccessible. -/
@[tactic checkHamiltonianTactic]
unsafe def checkHamiltonianTacticImpl : Tactic.Tactic
  | `(tactic|check_hamiltonian $g) => assertHamiltonicityFact g .anonymous
  | `(tactic|check_hamiltonian $g with $h) => assertHamiltonicityFact g h.getId
  | _ => throwUnsupportedSyntax

syntax (name := checkHamiltonianaTactic) "check_hamiltoniana " ident : tactic
/-- `check_hamiltoniana G` is `check_hamiltonian G` followed by `assumption`, in the same spirit
    as `simpa` for `simp`: it derives the fact about Hamiltonian cycles in `G` and then uses it
    to close the goal, rather than leaving it in the context. Like `check_hamiltonian`, it
    decides Hamiltonicity in both directions:

    ```lean
    example : Cycle7.isHamiltonian := by
      check_hamiltoniana Cycle7

    example : ¬Path3.isHamiltonian := by
      check_hamiltoniana Path3
    ```

    Unlike `check_traceablea`, there is no asymmetry to watch for between the two cases: the
    derived hypothesis is `G.isHamiltonian` or `¬ G.isHamiltonian` on the nose, never an
    unfolded existential, so it closes a goal stated either way.

    Use `check_hamiltonian` when the derived fact is a step rather than the whole proof.
-/
@[tactic checkHamiltonianaTactic]
unsafe def checkHamiltonianaTacticImpl : Tactic.Tactic
  | `(tactic|check_hamiltoniana $g) => do
    assertHamiltonicityFact g .anonymous
    Tactic.withMainContext do
      Tactic.liftMetaTactic fun mvarId => do
        try
          mvarId.assumption
          return []
        catch _ =>
          throwError "check_hamiltoniana derived a fact about Hamiltonian cycles in {g}, but it \
            does not close the goal. Use `check_hamiltonian {g} with h` to name it and finish \
            the proof by hand."

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Hypohamiltonicity
------------------------------------------

/-- What `searchForHypohamiltonicityAux` established, and why. As on the path side, the two
negative cases are kept apart so that a failure at a particular deletion can name the vertex. -/
inductive HypohamiltonicityOutcome
  /-- No Hamiltonian cycle, but every one-vertex deletion has one. -/
  | hypohamiltonian
  /-- Not hypohamiltonian: the graph is itself Hamiltonian. -/
  | hamiltonian
  /-- Not hypohamiltonian: neither the graph nor the deletion of this vertex is Hamiltonian. -/
  | deletionNotHamiltonian (v : Nat)

/-- Decide hypohamiltonicity of `graph`, and return the fact that establishes, a proof of it,
and which case it fell into.

The definition is checked in the order it is written: `graph` itself must fail to be Hamiltonian,
and then every `graph.deleteVertex v` must be Hamiltonian. Either question settling the matter
stops the search, so a negative answer costs only as many calls as it takes to reach the witness,
while a positive one costs `graph.vertexSize + 1`.

No size guard is needed here, unlike on the path side: `searchForHamiltonianCycleAux` answers at
every size without consulting the solver where the encoding would not apply. A graph with no
vertices comes out hypohamiltonian — not Hamiltonian for want of a vertex to base a cycle at,
with nothing to delete — and the empty `Fin.cases` chain proves the vacuous half.

`register` is passed through to each underlying call, so under `#check_hypohamiltonian` every
deletion leaves its own reusable certificate, named after the deletion. -/
unsafe def searchForHypohamiltonicityAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × HypohamiltonicityOutcome) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  let (_, proofG, outcomeG) ← searchForHamiltonianCycleAux graphName graph register
  match outcomeG with
  | .sat | .vacuous =>
    let proof ← Meta.mkAppM ``not_hypohamiltonian_of_hamiltonian #[proofG]
    return (q(¬ Graph.hypohamiltonian $graph), proof, .hamiltonian)
  | .unsat | .twoVertices | .noVertices =>
    -- The index plumbing is built with `Meta` rather than quoted: a `Q(…)` mentioning the loop
    -- variable's literal sends Qq looking for a compile-time value of it and fails in
    -- `reduceEval`.
    let vsize : Q(Nat) := q(Graph.vertexSize $graph)
    let mut proofs : Array Expr := #[]
    for i in [0:G.vertexSize] do
      let iLit := mkNatLit i
      let hLt ← Meta.mkDecideProof (← Meta.mkAppM ``LT.lt #[iLit, vsize])
      let v ← Meta.mkAppM ``Fin.mk #[iLit, hLt]
      let sub : Q(Graph) ← Meta.mkAppM ``Graph.deleteVertex #[graph, v]
      let subName : Name := .str graphName s!"deleteVertex{i}"
      let (_, proofSub, outcomeSub) ← searchForHamiltonianCycleAux subName sub register
      match outcomeSub with
      | .sat | .vacuous => proofs := proofs.push proofSub
      | .unsat | .twoVertices | .noVertices =>
        let proof ← Meta.mkAppM ``not_hypohamiltonian_of_deletion #[v, proofSub]
        return (q(¬ Graph.hypohamiltonian $graph), proof, .deletionNotHamiltonian i)
    let forallType : Q(Prop) :=
      q(∀ (v : Graph.vertex $graph), Graph.isHamiltonian (Graph.deleteVertex $graph v))
    let forallProof ← mkForallVertexProof forallType proofs
    let proof ← Meta.mkAppM ``hypohamiltonian_of_deletions #[proofG, forallProof]
    return (q(Graph.hypohamiltonian $graph), proof, .hypohamiltonian)

syntax (name := checkHypohamiltonian) "#check_hypohamiltonian " ident : command
/-- `#check_hypohamiltonian G` decides whether `G` is hypohamiltonian — has no Hamiltonian
    cycle, while `G - v` has one for every vertex `v` — by running the Hamiltonian cycle search
    on `G` and on each of its one-vertex deletions.
    The Petersen graph is the smallest nontrivial example.

    It reports which of the three ways the answer came out: hypohamiltonian, not
    hypohamiltonian because `G` is itself Hamiltonian, or not hypohamiltonian because some
    `G - v` is not. In the last case the vertex is named.

    Each underlying search registers its own certificate, so the deletions are left behind as
    `G.deleteVertexᵢ.HamiltonianCycleI` instances, and the UNSAT halves as axioms named after
    the graph they refute.

    This is the *command* form: it reports what it found and proves nothing about the current
    goal. Use the `check_hypohamiltonian` tactic for that.
-/
@[command_elab checkHypohamiltonian]
unsafe def checkHypohamiltonianImpl : Command.CommandElab
  | `(#check_hypohamiltonian $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, outcome) ← searchForHypohamiltonicityAux graphName graph (register := true)
    match outcome with
    | .hypohamiltonian =>
      logInfo m!"{graphName} is hypohamiltonian: it has no Hamiltonian cycle, but deleting \
        any single vertex leaves a graph that has one"
    | .hamiltonian =>
      logInfo m!"{graphName} is not hypohamiltonian: it has a Hamiltonian cycle"
    | .deletionNotHamiltonian v =>
      logInfo m!"{graphName} is not hypohamiltonian: it has no Hamiltonian cycle, but neither \
        does the graph left by deleting vertex {v}"

  | _ => throwUnsupportedSyntax

/-- Run the hypohamiltonicity search on `g` and add what it establishes to the local context as
a hypothesis named `h`: `g.hypohamiltonian`, or `¬ g.hypohamiltonian`. -/
unsafe def assertHypohamiltonicityFact (g : Ident) (h : Name) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (type, proof, _) ← searchForHypohamiltonicityAux g.getId graph (register := false)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h type proof
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

syntax (name := checkHypohamiltonianTactic) "check_hypohamiltonian " ident (" with" (ppSpace colGt ident))? : tactic
/-- `check_hypohamiltonian G` decides hypohamiltonicity of `G` with the SAT solver and adds the
    result to the local context as a hypothesis — `G.hypohamiltonian` or its negation, whichever
    the search established, so it serves goals of both signs. The hypothesis is the fact as
    stated in both cases, nothing left unfolded.

    **This tactic adds a hypothesis; it does not close the goal.** Finish with `assumption`.
    `check_hypohamiltonian G with h` names the hypothesis instead of leaving it inaccessible:

    ```lean
    example : Petersen.hypohamiltonian := by
      check_hypohamiltonian Petersen with h
      exact h
    ```

    A positive answer needs `¬ G.isHamiltonian` from the solver, so it depends on one
    unsatisfiability axiom; the cycles in the deletions are actual cycles and cost nothing.
-/
@[tactic checkHypohamiltonianTactic]
unsafe def checkHypohamiltonianTacticImpl : Tactic.Tactic
  | `(tactic|check_hypohamiltonian $g) => assertHypohamiltonicityFact g .anonymous
  | `(tactic|check_hypohamiltonian $g with $h) => assertHypohamiltonicityFact g h.getId
  | _ => throwUnsupportedSyntax

syntax (name := checkHypohamiltonianaTactic) "check_hypohamiltoniana " ident : tactic
/-- `check_hypohamiltoniana G` is `check_hypohamiltonian G` followed by `assumption`, in the
    same spirit as `simpa` for `simp`: it decides hypohamiltonicity of `G` and uses the result
    to close the goal, rather than leaving it in the context. Like `check_hypohamiltonian`, it
    decides the question in both directions:

    ```lean
    example : Petersen.hypohamiltonian := by
      check_hypohamiltoniana Petersen

    example : ¬Cycle7.hypohamiltonian := by
      check_hypohamiltoniana Cycle7
    ```

    Use `check_hypohamiltonian` when the derived fact is a step rather than the whole proof.
-/
@[tactic checkHypohamiltonianaTactic]
unsafe def checkHypohamiltonianaTacticImpl : Tactic.Tactic
  | `(tactic|check_hypohamiltoniana $g) => do
    assertHypohamiltonicityFact g .anonymous
    Tactic.withMainContext do
      Tactic.liftMetaTactic fun mvarId => do
        try
          mvarId.assumption
          return []
        catch _ =>
          throwError "check_hypohamiltoniana derived a fact about hypohamiltonicity of {g}, \
            but it does not close the goal. Use `check_hypohamiltonian {g} with h` to name it \
            and finish the proof by hand."

  | _ => throwUnsupportedSyntax

end LeanHoG
