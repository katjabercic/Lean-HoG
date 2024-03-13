import Lean
import Qq
import LeanHoG.SetTree
import LeanHoG.MapTree
import LeanHoG.Graph
import LeanHoG.Connectivity
import LeanHoG.Certificate
import LeanHoG.JsonData

import LeanSAT
import LeanHoG.Invariants.Hamiltonicity.SatEncoding

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

syntax (name := loadGraph) "load_graph" ident str (" tryHam ")? : command

@[command_elab loadGraph]
unsafe def loadGraphImpl : CommandElab
  | `(load_graph $graphName $fileName tryHam ) => do
    let graphName := graphName.getId
    let gapData ← loadGAPData fileName.getString
    have graphQ := graphOfData gapData.graph
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

    -- load the connectivity certificate, if present
    match gapData.connectivityData? with
    | .none => pure ()
    | .some data =>
      let connectivityCertificateName := certificateName graphName "connectivityCertificateI"
      let connectivityCertificateQ : Q(ConnectivityCertificate $graph) := connectivityCertificateOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := connectivityCertificateName
        levelParams := []
        type := q(ConnectivityCertificate $graph)
        value := connectivityCertificateQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance connectivityCertificateName .scoped 42

    -- load the disconnectivity certificate, if present
    match gapData.disconnectivityData? with
    | .none => pure ()
    | .some data =>
      let disconnectivityCertificateName := certificateName graphName "disconnectivityCertificateI"
      let disconnectivityCertificateQ : Q(DisconnectivityCertificate $graph) := disconnectivityCertificateOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := disconnectivityCertificateName
        levelParams := []
        type := q(DisconnectivityCertificate $graph)
        value := disconnectivityCertificateQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance disconnectivityCertificateName .scoped 42

    match gapData.pathData? with
    | .none =>
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

  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let gapData ← loadGAPData fileName.getString
    have graphQ := graphOfData gapData.graph
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

    -- load the connectivity certificate, if present
    match gapData.connectivityData? with
    | .none => pure ()
    | .some data =>
      let connectivityCertificateName := certificateName graphName "connectivityCertificateI"
      let connectivityCertificateQ : Q(ConnectivityCertificate $graph) := connectivityCertificateOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := connectivityCertificateName
        levelParams := []
        type := q(ConnectivityCertificate $graph)
        value := connectivityCertificateQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance connectivityCertificateName .scoped 42

    -- load the disconnectivity certificate, if present
    match gapData.disconnectivityData? with
    | .none => pure ()
    | .some data =>
      let disconnectivityCertificateName := certificateName graphName "disconnectivityCertificateI"
      let disconnectivityCertificateQ : Q(DisconnectivityCertificate $graph) := disconnectivityCertificateOfData graph data
      Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
        name := disconnectivityCertificateName
        levelParams := []
        type := q(DisconnectivityCertificate $graph)
        value := disconnectivityCertificateQ
        hints := .regular 0
        safety := .safe
      }
      Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance disconnectivityCertificateName .scoped 42

    match gapData.pathData? with
    | .none =>
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

  | _ => throwUnsupportedSyntax

end LeanHoG
