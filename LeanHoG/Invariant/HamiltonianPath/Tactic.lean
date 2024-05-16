import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

import LeanSAT

namespace LeanHoG

open Lean Elab Qq

open LeanSAT Model in
unsafe def searchForHamiltonianPathAux (graphName : Name) (graph : Q(Graph)) :
  TermElabM (Expr × Expr × Solver.Res) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  let enc := (hamiltonianPathCNF G).val
  let opts ← getOptions
  let cadicalExe := opts.get leanHoG.solverCmd.name leanHoG.solverCmd.defValue
  let cake_lprExr := opts.get leanHoG.proofCheckerCmd.name leanHoG.proofCheckerCmd.defValue
  let solver := SolverWithCakeLpr.SolverWithCakeLpr cadicalExe #["--no-binary", "--lrat=true"] cake_lprExr
  let cnf := Encode.EncCNF.toICnf enc
  let (_, s) := Encode.EncCNF.run enc
  let res ← solver.solve cnf
  match res with
  | .sat assn =>
    -- Build a Hamiltonian path from the solution given by the SAT solver
    let mut path : Array Nat := Array.mkArray G.vertexSize 0
    for i in List.fins G.vertexSize do
      for j in List.fins G.vertexSize do
        match assn.find? (s.vMap (Var.mk i j))  with
        | none => throwError "invalid index ({i},{j})"
        | some true => path := path.set! j i
        | some false => continue
    let hpQ := hamiltonianPathOfData graph ⟨path.toList⟩
    -- Add a Hamiltonian path instance from the constructed path
    let hamiltonianPathName := concatenateName graphName "HamiltonianPathI"
    Lean.addAndCompile <| .defnDecl {
      name := hamiltonianPathName
      levelParams := []
      type := q(HamiltonianPath $graph)
      value := hpQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Meta.addInstance hamiltonianPathName .scoped 42
    let existsHamPath ← Meta.mkAppM ``LeanHoG.HamiltonianPath.path_of_cert #[]
    let existsType := q(Graph.traceable $graph)
    return (existsType, existsHamPath, res)

  | .unsat =>
    -- The formula is UNSAT, add an axiom saying so
    let declName : Name := .str graphName "noHamiltonianPathCertificateExists"
    let type : Q(Prop) := q(¬ (∃ (τ : PropAssignment (Var (Graph.vertexSize $graph))), τ |> hamiltonianPathConstraints $graph))
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
    let noExistsCert ← Qq.elabTermEnsuringTypeQ (mkIdent declName) type
    let noExistsHamPath ← Meta.mkAppM ``LeanHoG.no_assignment_implies_no_hamiltonian_path' #[noExistsCert]
    let noExistsType := q(¬ ∃ (u v : Graph.vertex $graph) (p : Path $graph u v), p.isHamiltonian)
    return (noExistsType, noExistsHamPath, res)

  | .error => throwError "SAT solver exited with error"


------------------------------------------
-- Find Hamiltonian path command
------------------------------------------

syntax (name := checkTraceable) "#check_traceable " ident : command
/-- `#check_nontraceable G` runs a SAT solver on the encoding of the Hamiltonian path problem
    on the graph `G` and if the SAT solver says the problem is unsat it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding.
-/
@[command_elab checkTraceable]
unsafe def checkTraceableImpl : Command.CommandElab
  | `(#check_traceable $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (declName, _, res) ← searchForHamiltonianPathAux graphName graph
    match res with
    | .sat _ => logInfo m!"found Hamiltonian path {declName}"
    | .unsat => logInfo m!"no Hamiltonian path found after exhaustive search"
    | .error => throwError "SAT solver exited with error"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian path tactic
------------------------------------------
-- TODO: Remove code duplication once I figure out how to do it corectly.

syntax (name := checkTraceableTactic) "check_traceable " ident (" with" (ppSpace colGt ident))? : tactic
open LeanSAT Model in
/-- `#check_traceable G` runs a SAT solver on the encoding of the Hamiltonian path problem
    on the graph `G` and if the SAT solver says the problem is unsatisfiable it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding. The tactic uses the new axiom to
    deduce that there is no Hamiltonian path in the graph by using theorem and adds it
    as a hypothesis to the current context.

    Can also use `#check_traceable G with h` to save the hypothesis into the variable `h`.
-/
@[tactic checkTraceableTactic]
unsafe def checkTraceableTacticImpl : Tactic.Tactic
  | `(tactic|check_traceable $g) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      let (val, type, _) ← searchForHamiltonianPathAux graphName graph
      Tactic.liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert .anonymous val type
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]

  | `(tactic|check_traceable $g with $ident) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      let (val, type, _) ← searchForHamiltonianPathAux graphName graph
      Tactic.liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert ident.getId val type
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]

  | _ => throwUnsupportedSyntax

end LeanHoG
