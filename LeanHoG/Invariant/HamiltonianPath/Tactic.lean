import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

import Trestle.Encode.EncCNF

namespace LeanHoG

open Lean Elab Qq

/-- Whether `declName` already holds a declaration of type `expectedType`, which a
    previous run on the same graph would have left there and which can therefore be
    reused instead of declared again.

    The name existing is not on its own evidence that it holds such a declaration: the
    names below are derived from the graph's, and nothing stops anything else in the
    environment from having claimed one first. Reusing whatever is there would build a
    term against the wrong type and only fail later, in the kernel, complaining about a
    term the user never wrote. So a name held by something of another type is reported
    here instead; the name is taken either way, and there is nothing useful to do but
    say so.

    The comparison runs at a new metavariable depth so that a mismatch cannot leave
    `expectedType`'s metavariables assigned behind it. -/
private def hasReusableDecl (declName : Name) (expectedType : Expr) : Meta.MetaM Bool := do
  let some info := (← getEnv).find? declName | return false
  if ← Meta.withNewMCtxDepth (Meta.isDefEq info.type (← instantiateMVars expectedType)) then
    return true
  else
    throwError "the name {declName} is already taken by a declaration of type\
      {indentExpr info.type}\nbut this graph needs one of type{indentExpr expectedType}"

open Trestle Model in
/-- Decide traceability of `graph` with the SAT solver, and return the fact that
    establishes, a proof of it, and the solver's answer.

    `register` says whether that fact should be backed by a declaration named after
    the *graph*: the `HamiltonianPath` instance in the SAT case, the axiom in the
    UNSAT case. The `#check_traceable` command wants one, since registering a
    reusable certificate is the whole point of the command and
    `#show_hamiltonian_path` looks the instance up by name.

    The `check_traceable` tactics must not ask for one. Lean elaborates declarations
    in parallel and lets each add only names beneath its own prefix, so a named
    theorem cannot introduce `G.HamiltonianPathI` and fails with `cannot add
    declaration ... as it is restricted to the prefix ...`. With
    `register := false` the certificate is placed in the proof term directly, and
    the axiom — which has to be a declaration, there being no other way to assert
    one — is named beneath the declaration being elaborated. Either way an
    equivalent declaration already in the environment is reused. -/
unsafe def searchForHamiltonianPathAux (graphName : Name) (graph : Q(Graph))
    (register : Bool) : TermElabM (Expr × Expr × Solver.Res) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  let enc := (hamiltonianPathCNF G).val
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
    -- Build a Hamiltonian path from the solution given by the SAT solver
    let mut path : Array Nat := Array.replicate G.vertexSize 0
    for i in List.fins G.vertexSize do
      for j in List.fins G.vertexSize do
        match assn.findEntry? (s.vMap (Var.mk i j))  with
        | none => throwError "invalid index ({i},{j})"
        | some (_, true) => path := path.set! j i
        | some (_, false) => continue
    let hpQ := hamiltonianPathOfData graph ⟨path.toList⟩
    -- The certificate to hand to `path_of_cert`. `hamiltonianPathOfData` returns a
    -- self-contained term, so a declaration is a convenience and never a necessity:
    -- it makes the certificate reusable and visible to instance synthesis.
    --
    -- The name is a function of the graph's, so a second run on the same graph —
    -- `#check_traceable G` and then the tactic, or the tactic twice — would be
    -- re-declaring it. A `HamiltonianPath $graph` already in the environment is a
    -- certificate for the same graph, so reuse it rather than failing; that it is one,
    -- and not merely something sitting on the name, is what `hasReusableDecl` checks.
    let hamiltonianPathName := certificateName graphName "HamiltonianPathI"
    let certType : Q(Type) := q(HamiltonianPath $graph)
    let cert : Expr ←
      if ← hasReusableDecl hamiltonianPathName certType then
        pure (mkConst hamiltonianPathName)
      else if register then do
        Lean.addAndCompile <| .defnDecl {
          name := hamiltonianPathName
          levelParams := []
          type := certType
          value := hpQ
          hints := .regular 0
          safety := .safe
        }
        Lean.Meta.addInstance hamiltonianPathName .global 42
        pure (mkConst hamiltonianPathName)
      else
        pure hpQ
    -- Applied to the certificate explicitly, not left to instance synthesis: `mkAppM`
    -- with no arguments returns the bare constant, whose implicit `G` and instance
    -- are still abstracted, and that only fails later in the kernel.
    let existsHamPath ← Meta.mkAppOptM ``LeanHoG.HamiltonianPath.path_of_cert
      #[graph, cert]
    let existsType := q(Graph.traceable $graph)
    return (existsType, existsHamPath, res)

  | .unsat =>
    -- The formula is UNSAT, so we will assert an axiom saying so.
    --
    -- Everything that can fail is done *before* `addDecl`. Deriving the
    -- conclusion from the axiom is the expensive part, and if it is done after
    -- the axiom is in the environment then running out of heartbeats there
    -- leaves the axiom behind on a command that reports failure — the user sees
    -- an error but still has the hole. So the derivation is built against a
    -- local hypothesis of the axiom's type, and the axiom is only committed
    -- once that has succeeded.
    let globalName : Name := .str graphName "hamiltonianPathCNFUnsat"
    let type : Q(Prop) := q(((hamiltonianPathCNF $graph).val.toICnf.toStd).Unsat)
    let noExistsType := q(¬ ∃ (u v : Graph.vertex $graph) (p : Path $graph u v), p.isHamiltonian)
    -- Where the axiom goes. One for this graph already in the environment says
    -- exactly what is needed — literally so, which is what `hasReusableDecl` confirms
    -- before we lean on it — so reuse it; that is the case a second run on the
    -- same graph used to die on. Otherwise declare it, globally for the command and
    -- beneath the enclosing declaration for a tactic, which may not add a name
    -- outside its own prefix.
    let declName : Name ←
      if (← hasReusableDecl globalName type) ∨ register then
        pure globalName
      else
        match ← Term.getDeclName? with
        | some enclosing => pure (enclosing ++ globalName)
        | none => pure globalName
    -- `fun h => no_assignment_implies_no_hamiltonian_path' (std_unsat_implies_no_assignment h)`
    let derivation ← Meta.withLocalDeclD `hCnfUnsat type fun h => do
      let noExistsCert ← Meta.mkAppM ``LeanHoG.std_unsat_implies_no_assignment #[h]
      let noExistsHamPath ← Meta.mkAppM ``LeanHoG.no_assignment_implies_no_hamiltonian_path' #[noExistsCert]
      Meta.mkLambdaFVars #[h] (← instantiateMVars noExistsHamPath)
    unless ← hasReusableDecl declName type do
      let decl := Declaration.axiomDecl {
        name        := declName,
        levelParams := [],
        type        := type,
        isUnsafe    := false
      }
      trace[Elab.axiom] "{declName} : {type}"
      Term.ensureNoUnassignedMVars decl
      -- Past this point nothing but `addDecl` itself can fail.
      addDecl decl
      logWarning m!"added axiom {declName} : {type}"
    return (noExistsType, .app derivation (mkConst declName), res)

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
    | .sat _ =>
      logInfo m!"found Hamiltonian path, registered as \
        {certificateName graphName "HamiltonianPathI"}"
    | .unsat => logInfo m!"no Hamiltonian path found after exhaustive search"
    | .error => throwError "SAT solver exited with error"

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

end LeanHoG
