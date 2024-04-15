import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding
import LeanHoG.Invariant.HamiltonianCycle.Certificate
import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

import LeanSAT

namespace LeanHoG

open HamiltonianCycle Lean Elab Qq

open LeanSAT Model in
unsafe def searchForHamiltonianCycleAux (graph : Q(Graph)) :
  TermElabM (Option Expr) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  if h : 0 < G.vertexSize then
    let enc := (hamiltonianCycleCNF G h).val
    let opts ← getOptions
    let solverExe := opts.get leanHoG.solverCmd.name leanHoG.solverCmd.defValue
    let checkerExe := opts.get leanHoG.proofCheckerCmd.name leanHoG.proofCheckerCmd.defValue
    let solver := SolverWithCakeLpr.SolverWithCakeLpr solverExe #["--no-binary", "--lrat=true"] checkerExe
    let cnf := Encode.EncCNF.toICnf enc
    let (_, s) := Encode.EncCNF.run enc
    let res ← solver.solve cnf
    match res with
    | .sat assn =>
      -- Build a Hamiltonian cycle from the solution given by the SAT solver
      let mut cycle : Array Nat := Array.mkArray (G.vertexSize+1) 0
      for i in List.fins G.vertexSize do
        for j in List.fins (G.vertexSize+1) do
          match assn.find? (s.vMap (Var.mk i j))  with
          | none => throwError "invalid index ({i},{j})"
          | some true => cycle := cycle.set! j i
          | some false => continue
      let hpQ := hamiltonianCycleOfData graph ⟨cycle.toList⟩
      return some hpQ
    | .unsat =>
      -- TODO: Not yet implemented
      return none
    | .error => throwError "SAT solver exited with error"
  else
    throwError "cannot construct Hamiltonian cycle for empty graph"


------------------------------------------
-- Find Hamiltonian cycle command
------------------------------------------

unsafe def checkHamiltonianCycleAux (graphName : Name) (graph : Q(Graph)) : TermElabM Bool := do
  -- Check if there already exists an instance of a Hamiltonian cycle for g
  let inst ← Qq.trySynthInstanceQ q(HamiltonianCycle $graph)
  match inst with
  | .some _ =>
    logInfo "Hamiltonian cycle found"
    return true
  | _ =>
    let hpQOpt ← searchForHamiltonianCycleAux graph
    match hpQOpt with
    | some hpQ =>
      let hamiltonianCycleName := certificateName graphName "HamiltonianCycleI"
      Lean.addAndCompile <| .defnDecl {
        name := hamiltonianCycleName
        levelParams := []
        type := q(HamiltonianCycle $graph)
        value := hpQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Meta.addInstance hamiltonianCycleName .scoped 42
      logInfo "Hamiltonian cycle found"
      return true
    | none =>
      logWarning s!"Hamiltonian cycle not found after exhaustive search"
      return false

syntax (name := checkHamiltonian) "#check_hamiltonian " ident : command
/-- `#check_hamiltonian G` runs a SAT solver on the encoding of the Hamiltonian cycle problem
    on the graph `G` and if the SAT solver says the problem is unsat it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding.
-/
@[command_elab checkHamiltonian]
unsafe def checkHamiltonianImpl : Command.CommandElab
  | `(#check_hamiltonian $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let _ ← checkHamiltonianCycleAux graphName graph

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian cycle tactic
------------------------------------------
-- TODO: Remove code duplication once I figure out how to do it corectly.

unsafe def checkHamiltonianTacticAux (graphName : Name) (graph : Q(Graph)) (hypName : Name) :
  Tactic.TacticM Unit := do
  let isHamiltonian ← checkHamiltonianCycleAux graphName graph
  if isHamiltonian then
    let existsHamPath ← Meta.mkAppM ``LeanHoG.HamiltonianPath.path_of_cert #[]
    let existsType := q(Graph.traceable $graph)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert hypName existsHamPath existsType
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]
  else
    throwError "cannot prove non-Hamiltonicity, not implemented!"

syntax (name := checkHamiltonianTactic) "check_hamiltonian " ident (" with" (ppSpace colGt ident))? : tactic
open LeanSAT Model in
/-- `#check_hamiltonian G` runs a SAT solver on the encoding of the Hamiltonian cycle problem
    on the graph `G` and if the SAT solver says the problem is unsatisfiable it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding. The tactic uses the new axiom to
    deduce that there is no Hamiltonian cycle in the graph by using theorem and adds it
    as a hypothesis to the current context.
-/
@[tactic checkHamiltonianTactic]
unsafe def checkHamiltonianTacticImpl : Tactic.Tactic
  | `(tactic|check_hamiltonian $g) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      checkHamiltonianTacticAux graphName graph .anonymous

  | `(tactic|check_hamiltonian $g with $h) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      checkHamiltonianTacticAux graphName graph h.getId

  | _ => throwUnsupportedSyntax

end LeanHoG
