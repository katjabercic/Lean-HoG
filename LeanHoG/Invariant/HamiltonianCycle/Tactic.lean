import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding
import LeanHoG.Invariant.HamiltonianCycle.Certificate
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

open Trestle Model in
/-- Decide Hamiltonicity of `graph` with the SAT solver, and return the fact that
    establishes, a proof of it, and the solver's answer.

    `register` says whether that fact should be backed by a declaration named after
    the *graph*: the `HamiltonianCycle` instance in the SAT case. In the UNSAT case
    there is, as yet, no theorem deriving `¬ graph.isHamiltonian` from the encoding
    being unsatisfiable (that requires `HamiltonianCycle/Correctness.lean`, which does
    not exist yet — see `HamiltonianPath/Correctness.lean` for what the path version
    looks like). So in the UNSAT case this only returns the fact that the *encoding*
    is UNSAT, checked by Lean's verified LRAT checker; it is on the caller to present
    that honestly rather than as "no Hamiltonian cycle".

    See `LeanHoG.Invariant.HamiltonianPath.Tactic.searchForHamiltonianPathAux` for why
    `register` must be `false` from a tactic. -/
unsafe def searchForHamiltonianCycleAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × Solver.Res) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  if h : 0 < G.vertexSize then
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
      -- The certificate to hand to `cycle_of_cert`. As with the path version, a
      -- declaration is a convenience (reusable, visible to instance synthesis) and
      -- never a necessity: `hamiltonianCycleOfData` returns a self-contained term.
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
      let existsType := q(Graph.isHamiltonian $graph)
      return (existsType, existsHamCycle, res)

    | .unsat =>
      -- The formula is UNSAT, so we will assert an axiom saying so. This is as far as
      -- we can go without `HamiltonianCycle/Correctness.lean`: unlike the path version,
      -- there is no theorem yet deriving `¬ graph.isHamiltonian` from this, so the fact
      -- returned here is the *encoding's* unsatisfiability, not the graph's
      -- non-Hamiltonicity. Callers must not present the two as the same thing.
      let globalName : Name := .str graphName "hamiltonianCycleCNFUnsat"
      -- `h` is a proof about the concrete, evaluated `G`; the returned type must instead
      -- talk about `graph`, the quoted expression the caller wrote. Reflect the same fact
      -- at that level via `decide`, which is sound here because `h` already tells us it
      -- reduces to `true`.
      have hPos : Q(decide (0 < Graph.vertexSize $graph) = true) := (q(Eq.refl true) : Lean.Expr)
      let hQ : Q(0 < Graph.vertexSize $graph) := q(of_decide_eq_true $hPos)
      let type : Q(Prop) := q(((hamiltonianCycleCNF $graph $hQ).val.toICnf.toStd).Unsat)
      let declName : Name ←
        if (← hasReusableDecl globalName type) ∨ register then
          pure globalName
        else
          match ← Term.getDeclName? with
          | some enclosing => pure (enclosing ++ globalName)
          | none => pure globalName
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
      -- TODO(Correctness.lean): once the SAT-correctness proof for Hamiltonian cycles
      -- exists (mirroring `no_assignment_implies_no_hamiltonian_path'`), derive and
      -- return `¬ graph.isHamiltonian` here instead of the raw encoding fact.
      return (type, mkConst declName, res)

    | .error => throwError "SAT solver exited with error"
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
    an axiom asserting the encoding's unsatisfiability is added — but note that
    deriving `G.isNonHamiltonian` from it is **not yet implemented**
    (see `searchForHamiltonianCycleAux`), so this command cannot currently prove a
    graph non-Hamiltonian, only Hamiltonian.
-/
@[command_elab checkHamiltonian]
unsafe def checkHamiltonianImpl : Command.CommandElab
  | `(#check_hamiltonian $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, res) ← searchForHamiltonianCycleAux graphName graph (register := true)
    match res with
    | .sat _ =>
      logInfo m!"found Hamiltonian cycle, registered as \
        {certificateName graphName "HamiltonianCycleI"}"
    | .unsat =>
      logInfo m!"the encoding is unsatisfiable after exhaustive search, but deriving \
        non-Hamiltonicity from that is not yet implemented"
    | .error => throwError "SAT solver exited with error"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian cycle tactic
------------------------------------------

open Trestle Model in
/-- Run the Hamiltonian cycle search on `g` and add what it establishes to the local
    context as a hypothesis named `h`. On SAT that hypothesis is `g.isHamiltonian`; on
    UNSAT it is only the raw fact that the SAT encoding is unsatisfiable (see
    `searchForHamiltonianCycleAux` for why there is nothing stronger to offer yet). -/
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
    docstring, and the same caveat about the UNSAT case applies. This tactic adds a
    hypothesis; it does not close the goal.

    `check_hamiltonian G with h` names the hypothesis `h` instead of leaving it
    inaccessible. -/
@[tactic checkHamiltonianTactic]
unsafe def checkHamiltonianTacticImpl : Tactic.Tactic
  | `(tactic|check_hamiltonian $g) => assertHamiltonicityFact g .anonymous
  | `(tactic|check_hamiltonian $g with $h) => assertHamiltonicityFact g h.getId
  | _ => throwUnsupportedSyntax

end LeanHoG
