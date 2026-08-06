import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding
import LeanHoG.Invariant.HamiltonianCycle.Certificate
import LeanHoG.Invariant.HamiltonianCycle.Correctness
import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

import Trestle.Encode.EncCNF

namespace LeanHoG

open Lean Elab Qq
open HamiltonianCycle (hamiltonianCycleCNF)

/-- Whether `declName` already holds a declaration of type `expectedType`, which a
    previous run on the same graph would have left there and which can therefore be
    reused instead of declared again.

    See `LeanHoG.Invariant.HamiltonianPath.Tactic.hasReusableDecl` for the reasoning
    behind this check; it is duplicated here (rather than shared) because it is
    `private` there. -/
private def hasReusableDecl (declName : Name) (expectedType : Expr) : Meta.MetaM Bool := do
  let some info := (← getEnv).find? declName | return false
  if ← Meta.withNewMCtxDepth (Meta.isDefEq info.type (← instantiateMVars expectedType)) then
    return true
  else
    throwError "the name {declName} is already taken by a declaration of type\
      {indentExpr info.type}\nbut this graph needs one of type{indentExpr expectedType}"

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

/-- Turn a `HamiltonianCycle graph` certificate into the `graph.isHamiltonian` fact, backed
    by a declaration named after the graph when `register` says so.

    As with the path version, that declaration is a convenience (reusable across runs,
    visible to instance synthesis) and never a necessity: the certificate term stands on
    its own. -/
private def certifyHamiltonian (graphName : Name) (graph : Q(Graph)) (register : Bool)
    (hcQ : Q(HamiltonianCycle $graph)) : TermElabM (Expr × Expr) := do
  let hamiltonianCycleName := certificateName graphName "HamiltonianCycleI"
  let certType : Q(Type) := q(HamiltonianCycle $graph)
  let cert : Expr ←
    if ← hasReusableDecl hamiltonianCycleName certType then
      pure (mkConst hamiltonianCycleName)
    else if register then do
      Lean.addAndCompile <| .defnDecl {
        name := hamiltonianCycleName
        levelParams := []
        type := certType
        value := hcQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Meta.addInstance hamiltonianCycleName .global 42
      pure (mkConst hamiltonianCycleName)
    else
      pure hcQ
  let existsHamCycle ← Meta.mkAppOptM ``LeanHoG.HamiltonianCycle.cycle_of_cert
    #[graph, cert]
  return (q(Graph.isHamiltonian $graph), existsHamCycle)

open Trestle Model in
/-- Decide Hamiltonicity of `graph` with the SAT solver, and return the fact that
    establishes, a proof of it, and how it was established.

    `register` says whether that fact should be backed by a declaration named after
    the *graph*: the `HamiltonianCycle` instance when the graph is Hamiltonian, the
    axiom asserting the encoding's unsatisfiability when it is not.

    A one-vertex graph is answered without running the solver, and not as an optimisation:
    `hamiltonianCycleCNF` is unconditionally UNSAT there — `firstAndLastConstraints` puts
    vertex `0` at positions `0` and `1` both, which `edgeConstraints` then forbids, adjacency
    being irreflexive — while the graph itself is vacuously Hamiltonian. Consulting the
    solver would therefore report UNSAT for a Hamiltonian graph. This is also why
    `no_assignment_implies_no_hamiltonian_cycle'` carries `1 < G.vertexSize`.

    See `LeanHoG.Invariant.HamiltonianPath.Tactic.searchForHamiltonianPathAux` for why
    `register` must be `false` from a tactic. -/
unsafe def searchForHamiltonianCycleAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × HamiltonicityOutcome) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  if h2 : 1 < G.vertexSize then
    let h : 0 < G.vertexSize := Nat.zero_lt_of_lt h2
    let enc := (hamiltonianCycleCNF G h).val
    let opts ← getOptions
    let cadicalExe := opts.get leanHoG.solverCmd.name leanHoG.solverCmd.defValue
    let timeoutSec := opts.get leanHoG.solverTimeout.name leanHoG.solverTimeout.defValue
    let maxCertMB := opts.get leanHoG.maxCertificateSize.name leanHoG.maxCertificateSize.defValue
    let solver := SolverWithLRAT cadicalExe #["--no-binary", "--lrat=true"]
      { timeoutSec := timeoutSec, maxProofBytes := maxCertMB * 1024 * 1024 }
    let cnf := Encode.EncCNF.toICnf enc
    let (_, s) := Encode.EncCNF.run enc
    let res ← solver.solve cnf
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
      let solverBlame := m!"The solver named by `leanHoG.solverCmd` ({cadicalExe}) is \
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
      -- `fun hUnsat => no_assignment_implies_no_hamiltonian_cycle' h2
      --                  (std_unsat_implies_no_assignment h hUnsat)`.
      -- The two theorems disagree on which proof of `0 < G.vertexSize` appears in the
      -- assignment-free statement they share (`hQ` here, `by omega` from `h2` there); that
      -- is immaterial, as definitional proof irrelevance makes any two interchangeable.
      let derivation ← Meta.withLocalDeclD `hCnfUnsat type fun hUnsat => do
        let noAssignment ← Meta.mkAppM
          ``LeanHoG.HamiltonianCycle.std_unsat_implies_no_assignment #[hQ, hUnsat]
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
    throwError "cannot search for a Hamiltonian cycle in a graph with no vertices"

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

    A one-vertex graph never reaches the solver — it is vacuously Hamiltonian, which the
    encoding does not see (see `searchForHamiltonianCycleAux`).
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

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian cycle tactic
------------------------------------------

open Trestle Model in
/-- Run the Hamiltonian cycle search on `g` and add what it establishes to the local
    context as a hypothesis named `h`: `g.isHamiltonian` when a cycle is found (or when `g`
    is a single vertex), `¬ g.isHamiltonian` when the encoding is refuted. -/
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

end LeanHoG
