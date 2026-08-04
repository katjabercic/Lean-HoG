import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

import Trestle.Encode.EncCNF

namespace LeanHoG

open Lean Elab Qq

open Trestle Model in
unsafe def searchForHamiltonianPathAux (graphName : Name) (graph : Q(Graph)) :
  TermElabM (Expr × Expr × Solver.Res) := do
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
    -- Add a Hamiltonian path instance from the constructed path
    let hamiltonianPathName := certificateName graphName "HamiltonianPathI"
    -- The name is a function of the graph's, so a second run on the same graph —
    -- `#check_traceable G` and then the tactic, or the tactic twice — would be
    -- re-declaring it. The certificate already in the environment is a certificate
    -- for the same graph, so reuse it rather than failing.
    unless (← getEnv).contains hamiltonianPathName do
      Lean.addAndCompile <| .defnDecl {
        name := hamiltonianPathName
        levelParams := []
        type := q(HamiltonianPath $graph)
        value := hpQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Meta.addInstance hamiltonianPathName .global 42
    -- Applied to the certificate by name, not left to instance synthesis: `mkAppM`
    -- with no arguments returns the bare constant, whose implicit `G` and instance
    -- are still abstracted, and that only fails later in the kernel.
    let existsHamPath ← Meta.mkAppOptM ``LeanHoG.HamiltonianPath.path_of_cert
      #[graph, mkConst hamiltonianPathName]
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
    let declName : Name := .str graphName "hamiltonianPathCNFUnsat"
    let type : Q(Prop) := q(((hamiltonianPathCNF $graph).val.toICnf.toStd).Unsat)
    let noExistsType := q(¬ ∃ (u v : Graph.vertex $graph) (p : Path $graph u v), p.isHamiltonian)
    -- `fun h => no_assignment_implies_no_hamiltonian_path' (std_unsat_implies_no_assignment h)`
    let derivation ← Meta.withLocalDeclD `hCnfUnsat type fun h => do
      let noExistsCert ← Meta.mkAppM ``LeanHoG.std_unsat_implies_no_assignment #[h]
      let noExistsHamPath ← Meta.mkAppM ``LeanHoG.no_assignment_implies_no_hamiltonian_path' #[noExistsCert]
      Meta.mkLambdaFVars #[h] (← instantiateMVars noExistsHamPath)
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
    let (_, _, res) ← searchForHamiltonianPathAux graphName graph
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
    let (type, proof, _) ← searchForHamiltonianPathAux g.getId graph
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
