import Lean
import Qq

import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.Certificate
import LeanHoG.JsonData

import LeanSAT
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Invariant.HamiltonianPath.Certificate

namespace LeanHoG

open Qq Lean

/-- Lifting from exception monad to the Elab.Command monad -/
def liftExcept {α : Type} {m} [Monad m] [MonadError m] : Except String α → m α
  | .ok res => pure res
  | .error msg => throwError msg

/-- A Lean name for a certicicate -/
def certificateName (graphName: Name) (certName: String) : Name :=
  (.str graphName certName)

instance : LeanSAT.Solver IO := (LeanSAT.Solver.Impl.DimacsCommand "kissat")

syntax (name := loadGraph) "load_graph" ident str (" try_ham ")? : command

unsafe def loadGraphAux (graphName : Name) (jsonData : JSONData) : Elab.Command.CommandElabM Unit := do
  have graphQ := graphOfData jsonData.graph
  -- load the graph
  Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := q($graphQ)
    hints := .regular 0
    safety := .safe
  }
  setReducibleAttribute graphName
  have graph : Q(Graph) := mkConst graphName []

  match jsonData.connectedComponents? with
  | .none => pure ()
  | .some data =>
    let componentsCertificateName := certificateName graphName "CertificateI"
    let componentsCertificateQ : Q(ConnectedComponentsCertificate $graph) := connectedComponentsCertificateOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := componentsCertificateName
      levelParams := []
      type := q(ConnectedComponentsCertificate $graph)
      value := componentsCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance componentsCertificateName .scoped 42

  match jsonData.hamiltonianPath? with
  | .none => pure ()
  | .some data =>
    let hamiltonianPathName := certificateName graphName "HamiltonianPathI"
    let hpQ := hamiltonianPathOfData graph data
    Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
      name := hamiltonianPathName
      levelParams := []
      type := q(HamiltonianPath $graph)
      value := hpQ
      hints := .regular 0
      safety := .safe
    }
    Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance hamiltonianPathName .global 42
  match jsonData.bipartite? with
  | .none => pure ()
  | .some data =>
    let BipartiteCertificateName := certificateName graphName "BipartiteCertificateI"
    let BipartiteCertificateQ : Q(BipartiteCertificate $graph) := BipartiteCertificateOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := BipartiteCertificateName
      levelParams := []
      type := q(BipartiteCertificate $graph)
      value := BipartiteCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance BipartiteCertificateName .scoped 42

  match jsonData.oddClosedWalk? with
  | .none => pure ()
  | .some data =>
    let OddClosedWalkName := certificateName graphName "OddClosedWalkI"
    let OddClosedWalkQ : Q(OddClosedWalk $graph) := OddClosedWalkOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := OddClosedWalkName
      levelParams := []
      type := q(OddClosedWalk $graph)
      value := OddClosedWalkQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance OddClosedWalkName .scoped 42

  match jsonData.neighborhoodMap? with
  | .none => pure ()
  | .some data =>
    let neighborhoodMapName := certificateName graphName "neighborhoodMapI"
    let neighborhoodMapQ : Q(NeighborhoodMap $graph) := neighborhoodMapOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := neighborhoodMapName
      levelParams := []
      type := q(NeighborhoodMap $graph)
      value := neighborhoodMapQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance neighborhoodMapName .scoped 42


/-- Load a graph with the given Lean identifier from the given file. -/
@[command_elab loadGraph]
unsafe def loadGraphImpl : Elab.Command.CommandElab
  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData fileName.getString
    loadGraphAux graphName jsonData

  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
