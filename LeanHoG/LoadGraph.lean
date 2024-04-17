import Lean
import Qq

import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.RawHoG

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

  match jsonData.rawHoG? with
  | .none => pure ()
  | .some data =>
    have dataQ : Q(RawHoGData) := ToExpr.toExpr data
    let rawHoGName := certificateName graphName "RawHoGI"
    -- let rawHoGQ : Q(ConnectedComponentsCertificate $graph) := connectedComponentsCertificateOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := rawHoGName
      levelParams := []
      type := q(RawHoG $graph)
      value := q(@RawHoG.mk $graph $(dataQ))
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance rawHoGName .scoped 42

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

  match jsonData.twoColoring? with
  | .none => pure ()
  | .some data =>
    let TwoColoringName := certificateName graphName "TwoColoringI"
    let TwoColoringQ : Q(TwoColoring $graph) := TwoColoringOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := TwoColoringName
      levelParams := []
      type := q(TwoColoring $graph)
      value := TwoColoringQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance TwoColoringName .scoped 42

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



/-- `load_graph <ID> <file>` loads a graph into the given Lean identifier `ID` from the given file. -/
@[command_elab loadGraph]
unsafe def loadGraphImpl : Elab.Command.CommandElab
  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData JSONData fileName.getString
    loadGraphAux graphName jsonData

  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
