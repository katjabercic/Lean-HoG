import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Tactic.Options

import LeanSAT

namespace LeanHoG

open Lean Widget Elab Command Term Meta Qq LeanSAT Model Tactic

-- def loadHamiltonianPathData (filePath : System.FilePath) : IO HamiltonianPathData := do
--   let fileContent ← IO.FS.readFile filePath
--   match Lean.Json.parse fileContent >>= Lean.FromJson.fromJson? (α := HamiltonianPathData) with
--   | .ok data => pure data
--   | .error msg => throw (.userError msg)

syntax (name := computeHamiltonianPath) "#compute_hamiltonian_path " ident : command

@[command_elab computeHamiltonianPath]
unsafe def computeHamiltonianPathImpl : CommandElab
  | `(#compute_hamiltonian_path $g ) => liftTermElabM do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let G ← evalExpr' Graph ``Graph graph

    let opts ← getOptions
    let pythonExe := opts.get leanHoG.pythonExecutable.name leanHoG.pythonExecutable.defValue
    let output ← IO.Process.output {
      cmd := pythonExe
      args := #["Download/findHamiltonianPath.py", s!"{g.getId}", s!"{G.vertexSize}", s!"{toJson G.edgeSet.toList}"]
    }
    if output.exitCode ≠ 0 then
      throwError m!"could not find Hamiltonian path"

    let path : System.FilePath := System.mkFilePath ["build", "invariants", "hamiltonianPath", s!"{g.getId}.json"]
    let pathData ← loadJSONData HamiltonianPathData path
    let hamiltonianPathName := certificateName g.getId "HamiltonianPathI"
    let hpQ := hamiltonianPathOfData graph pathData
    Lean.addAndCompile <| .defnDecl {
      name := hamiltonianPathName
      levelParams := []
      type := q(HamiltonianPath $graph)
      value := hpQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Meta.addInstance hamiltonianPathName .scoped 42
    logInfo "found Hamiltonian path"

  | _ => throwUnsupportedSyntax

syntax (name := showNoHamiltonianPath) "#show_no_hamiltonian_path " ident : command

unsafe def showNoHamiltonianPathAux (graphName : Name) (graph : Q(Graph)) : TermElabM (Name × Q(Prop)) := do
    let G ← evalExpr' Graph ``Graph graph
    let enc := (hamiltonianPathCNF G).val
    -- let cadicalExe := "/home/jure/source-control/cadical/build/cadical"
    -- let cake_lprExr := "/home/jure/source-control/cake_lpr/cake_lpr"
    -- let solver := LeanSAT.Solver.Impl.CakeLpr cadicalExe #["--no-binary"] cake_lprExr
    let solver : LeanSAT.Solver IO := (LeanSAT.Solver.Impl.DimacsCommand "/home/jure/source-control/cadical/build/cadical")
    let cnf := Encode.EncCNF.toICnf enc
    let res ← solver.solve cnf
    match res with
    | .sat _sol =>
      throwError "graph has Hamiltonian path"
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
      return (declName, type)
    | .error => throwError "SAT solver exited with error"

/-- `#show_no_hamiltonian_path G` runs a SAT solver on the encoding of the Hamiltonian path problem
    on the graph `G` and if the SAT solver says the problem is unsat it runs the produced proof
    through a verified proof checker cake_lpr. If the checker agrees with the proof, we add an axiom
    saying there exists no satisfying assignmment for the encoding.
-/
@[command_elab showNoHamiltonianPath]
unsafe def showNoHamiltonianPathImpl : CommandElab
  | `(#show_no_hamiltonian_path $g ) => liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (declName, type) ← showNoHamiltonianPathAux graphName graph
    logInfo m!"added axiom {declName} : {type}"

  | _ => throwUnsupportedSyntax

syntax (name := showNoHamiltonianPathTactic) "show_no_hamiltonian_path " ident : tactic

@[tactic showNoHamiltonianPathTactic]
unsafe def showNoHamiltonianPathTacticImpl : Tactic
  | `(tactic|show_no_hamiltonian_path $g) =>
    withMainContext do
      let graphName := g.getId
      let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
      let (declName, type) ← showNoHamiltonianPathAux graphName graph
      let noExistsCert ← Tactic.elabTermEnsuringType (mkIdent declName) type
      let noExistsHamPath ← mkAppM ``LeanHoG.no_assignment_implies_no_hamiltonian_path' #[noExistsCert]
      let noExistsType := q(¬ ∃ (u v : Graph.vertex $graph) (p : Path $graph u v), p.isHamiltonian)
      liftMetaTactic fun mvarId => do
        let mvarIdNew ← mvarId.assert .anonymous noExistsType noExistsHamPath
        let (_, mvarIdNew) ← mvarIdNew.intro1P
        return [mvarIdNew]

  | _ => throwUnsupportedSyntax

end LeanHoG
