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
unsafe def searchForHamiltonianCycleAux (graphName : Name) (graph : Q(Graph)) :
  TermElabM (Expr × Expr × Solver.Res) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  let enc := (hamiltonianCycleCNF G).val
  let opts ← getOptions
  let cadicalExe := opts.get leanHoG.solverCmd.name leanHoG.solverCmd.defValue
  let cake_lprExr := opts.get leanHoG.proofCheckerCmd.name leanHoG.proofCheckerCmd.defValue
  let solver := SolverWithCakeLpr.SolverWithCakeLpr cadicalExe #["--no-binary", "--lrat=true"] cake_lprExr
  let cnf := Encode.EncCNF.toICnf enc
  let (_, s) := Encode.EncCNF.run enc
  let res ← solver.solve cnf
  match res with
  | .sat assn =>
    -- Build a Hamiltonian cycle from the solution given by the SAT solver
    let mut cycle : Array Nat := Array.mkArray G.vertexSize 0
    for i in List.fins G.vertexSize do
      for j in List.fins G.vertexSize do
        match assn.find? (s.vMap (Var.mk i j))  with
        | none => throwError "invalid index ({i},{j})"
        | some true => cycle := cycle.set! j i
        | some false => continue
    let hpQ := hamiltonianCycleOfData graph ⟨cycle.toList⟩
    -- Add a Hamiltonian cycle instance from the constructed cycle
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
    let existsHamCycle ← Meta.mkAppM ``LeanHoG.HamiltonianCycle.cycle_of_cert #[]
    let existsType := q(Graph.isHamiltonian $graph)
    return (existsType, existsHamCycle, res)

  | .unsat =>
    -- The formula is UNSAT, add an axiom saying so
    throwError "non-Hamiltonicity not yet implemented"

  | .error => throwError "SAT solver exited with error"


------------------------------------------
-- Find Hamiltonian cycle command
------------------------------------------

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
    let (declName, _, res) ← searchForHamiltonianCycleAux graphName graph
    match res with
    | .sat _ => logInfo m!"found Hamiltonian cycle {declName}"
    | .unsat => logInfo m!"no Hamiltonian cycle found after exhaustive search"
    | .error => throwError "SAT solver exited with error"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Find Hamiltonian cycle tactic
------------------------------------------
-- TODO: Remove code duplication once I figure out how to do it corectly.

syntax (name := checkHamiltonianTactic) "check_hamiltonian " ident (" with" (ppSpace colGt ident))? : tactic
open LeanSAT Model in
/-- `#check_hamiltonian G` runs a SAT solver on the encoding of the Hamiltonian cycle problem
    on the graph `G` and if the SAT solver says the problem is unsatisfiable it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding. The tactic uses the new axiom to
    deduce that there is no Hamiltonian cycle in the graph by using theorem and adds it
    as a hypothesis to the current context.

    Can also use `#check_hamiltonian G with h` to save the hypothesis into the variable `h`.
-/
@[tactic checkHamiltonianTactic]
unsafe def checkHamiltonianTacticImpl : Tactic.Tactic
  | `(tactic|check_hamiltonian $g) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      let (val, type, _) ← searchForHamiltonianCycleAux graphName graph
      Tactic.liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert .anonymous val type
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]

  | `(tactic|check_hamiltonian $g with $ident) =>
    Tactic.withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      let (val, type, _) ← searchForHamiltonianCycleAux graphName graph
      Tactic.liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert ident.getId val type
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]

  | _ => throwUnsupportedSyntax

end LeanHoG
