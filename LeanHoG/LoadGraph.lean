import Lean
import Qq

import LeanHoG.Graph
import LeanHoG.Invariant.Bipartiteness.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.Certificate
import LeanHoG.JsonData

import LeanSAT
import LeanHoG.Invariant.Hamiltonicity.SatEncoding
import LeanHoG.Invariant.Hamiltonicity.Certificate

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

unsafe def loadGraphAux (graphName : Name) (jsonData : JSONData) (tryHam : Bool) : Elab.Command.CommandElabM Unit := do
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

  match jsonData.pathData? with
  | .none =>
    if tryHam then
      let g ← Elab.Command.liftTermElabM (Meta.evalExpr Graph q(Graph) graph)
      let mbHp ← tryFindHamiltonianPath g
      match mbHp with
      | .none => pure ()
      | .some hp =>
        let data : PathData := { vertices := hp.vertices }
        let hamiltonianPathName := certificateName graphName "hamiltonianPath"
        let hpQ := hamiltonianPathOfData graph data
        Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
          name := hamiltonianPathName
          levelParams := []
          type := q(HamiltonianPath $graph)
          value := hpQ
          hints := .regular 0
          safety := .safe
        }
        Elab.Command.liftTermElabM <| Meta.addInstance hamiltonianPathName .scoped 42
    else
      pure ()
  | .some data =>
    let hamiltonianPathName := certificateName graphName "hamiltonianPath"
    let hpQ := hamiltonianPathOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := hamiltonianPathName
      levelParams := []
      type := q(HamiltonianPath $graph)
      value := hpQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance hamiltonianPathName .scoped 42

  match jsonData.bipartiteness? with
  | .none => pure ()
  | .some data =>
    let bipartitenessCertificateName := certificateName graphName "bipartitenessCertificateI"
    let bipartitenessCertificateQ : Q(BipartitenessCertificate $graph) := bipartitenessCertificateOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := bipartitenessCertificateName
      levelParams := []
      type := q(BipartitenessCertificate $graph)
      value := bipartitenessCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance bipartitenessCertificateName .scoped 42

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
  | `(load_graph $graphName $fileName try_ham ) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData fileName.getString
    loadGraphAux graphName jsonData true

  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData fileName.getString
    loadGraphAux graphName jsonData false

  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
