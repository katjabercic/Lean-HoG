import Lean
import Qq
import LeanHoG.Graph
--import LeanHoG.Connectivity
--import LeanHoG.Invariant.Connectivity.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Certificate
import LeanHoG.JsonData

import LeanSAT
import LeanHoG.Invariant.Hamiltonicity.SatEncoding
import LeanHoG.Invariant.Hamiltonicity.Certificate

namespace LeanHoG

open Qq LeanSAT Lean Meta Elab Command

/-- Lifting from exception monad to the Elab.Command monad -/
def liftExcept {α : Type} {m} [Monad m] [Lean.MonadError m] : Except String α → m α
  | .ok res => pure res
  | .error msg => throwError msg

/-- A Lean name for a certicicate -/
def certificateName (graphName: Lean.Name) (certName: String) : Lean.Name :=
  (.str graphName certName)

instance : Solver IO := (Solver.Impl.DimacsCommand "kissat")

syntax (name := loadGraph) "load_graph" ident str (" try_ham ")? : command

unsafe def loadGraphAux (graphName : Name) (jsonData : JSONData) (tryHam : Bool) : CommandElabM Unit := do
  have graphQ := graphOfData jsonData.graph
  -- load the graph
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := q($graphQ)
    hints := .regular 0
    safety := .safe
  }
  Lean.setReducibleAttribute graphName
  have graph : Q(Graph) := Lean.mkConst graphName []

    match jsonData.componentsData? with
    | .none => pure ()
    | .some data =>
      let componentsCertificateName := certificateName graphName "CertificateI"
      let componentsCertificateQ : Q(ComponentsCertificate $graph) := componentsCertificateOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := componentsCertificateName
        levelParams := []
        type := q(ComponentsCertificate $graph)
        value := componentsCertificateQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance componentsCertificateName .scoped 42

    match jsonData.pathData? with
    | .none =>
      if tryHam then
        let g ← Elab.Command.liftTermElabM (evalExpr Graph q(Graph) graph)
        let mbHp ← tryFindHamiltonianPath g
        match mbHp with
        | .none => pure ()
        | .some hp =>
          let data : PathData := { vertices := hp.vertices }
          let hamiltonianPathName := certificateName graphName "hamiltonianPath"
          let hpQ := hamiltonianPathOfData graph data
          Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
            name := hamiltonianPathName
            levelParams := []
            type := q(HamiltonianPath $graph)
            value := hpQ
            hints := .regular 0
            safety := .safe
          }
          Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance hamiltonianPathName .scoped 42
      else
        pure ()
    | .some data =>
      let hamiltonianPathName := certificateName graphName "hamiltonianPath"
      let hpQ := hamiltonianPathOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := hamiltonianPathName
        levelParams := []
        type := q(HamiltonianPath $graph)
        value := hpQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance hamiltonianPathName .scoped 42

@[command_elab loadGraph]
unsafe def loadGraphImpl : CommandElab
  | `(load_graph $graphName $fileName try_ham ) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData fileName.getString
    loadGraphAux graphName jsonData true

  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData fileName.getString
    loadGraphAux graphName jsonData false

  | _ => throwUnsupportedSyntax

#check loadGraphImpl

end LeanHoG
