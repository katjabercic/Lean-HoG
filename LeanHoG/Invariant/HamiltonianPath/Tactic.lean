import Lean
import Qq
import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Tactic.Options

namespace LeanHoG

open Lean Widget Elab Command Term Meta Qq

-- def loadHamiltonianPathData (filePath : System.FilePath) : IO HamiltonianPathData := do
--   let fileContent ← IO.FS.readFile filePath
--   match Lean.Json.parse fileContent >>= Lean.FromJson.fromJson? (α := HamiltonianPathData) with
--   | .ok data => pure data
--   | .error msg => throw (.userError msg)

syntax (name := computeHamiltonianPath) "#compute_hamiltonian_path " ident : command

open ProofWidgets in
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
      IO.eprintln f!"failed to download graphs: {output.stderr}"
      return

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

end LeanHoG
