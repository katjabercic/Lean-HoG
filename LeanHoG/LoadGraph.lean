import Lean
import Qq

import LeanHoG.Graph
import LeanHoG.Graph6
import LeanHoG.Invariant.G6
import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.Certificate
import LeanHoG.Util.Meta
import LeanHoG.JsonData

import Trestle.Solver.Impl.DimacsCommand
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

instance : Trestle.Solver IO := (Trestle.Solver.Impl.DimacsCommand "kissat")

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

  match jsonData.canonicalForm? with
  | .none => pure ()
  | .some g6 =>
    let g6Name : Name := (.str graphName "val")
    let g6Q : Q(G6 $graph) :=   q(G6.mk $g6)
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := g6Name
      levelParams := []
      type := q(G6 $graph)
      value := g6Q
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance g6Name .global 42

  match jsonData.connectedComponents? with
  | .none => pure ()
  | .some data =>
    let componentsCertificateName := certificateName graphName "ConnectedComponentsCertificateI"
    let componentsCertificateQ : Q(ConnectedComponentsCertificate $graph) := connectedComponentsCertificateOfData graph data
    Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
      name := componentsCertificateName
      levelParams := []
      type := q(ConnectedComponentsCertificate $graph)
      value := componentsCertificateQ
      hints := .regular 0
      safety := .safe
    }
    Elab.Command.liftTermElabM <| Meta.addInstance componentsCertificateName .global 42

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
    Elab.Command.liftTermElabM <| Meta.addInstance TwoColoringName .global 42

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
    Elab.Command.liftTermElabM <| Meta.addInstance OddClosedWalkName .global 42

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
    Elab.Command.liftTermElabM <| Meta.addInstance neighborhoodMapName .global 42



/-- `load_graph <ID> <file>` loads a graph into the given Lean identifier `ID` from the given file. -/
@[command_elab loadGraph]
unsafe def loadGraphImpl : Elab.Command.CommandElab
  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData JSONData fileName.getString
    loadGraphAux graphName jsonData

  | _ => Elab.throwUnsupportedSyntax

syntax (name := loadGraphFromG6) "load_graph_from_g6" ident str : command
syntax (name := loadGraphsFromG6File) "load_graphs_from_g6_file" ident str : command

/-- Present bare graph data as a `JSONData` carrying no invariant certificates. -/
def jsonDataOfGraphData (data : GraphData) : JSONData where
  hogId := none
  graph := data
  canonicalForm? := none
  connectedComponents? := none
  hamiltonianPath? := none
  twoColoring? := none
  oddClosedWalk? := none
  neighborhoodMap? := none

/-- `load_graph_from_g6 <ID> <g6>` loads the graph encoded by the graph6 string
    `<g6>` into the Lean identifier `ID`. -/
@[command_elab loadGraphFromG6]
unsafe def loadGraphFromG6Impl : Elab.Command.CommandElab
  | `(load_graph_from_g6 $graphName $g6) => do
    let data ← liftExcept <| Graph6.decode g6.getString
    loadGraphAux graphName.getId (jsonDataOfGraphData data)

  | _ => Elab.throwUnsupportedSyntax

/-- `load_graphs_from_g6_file <ID> <file>` loads every graph in a graph6 file,
    one per line, into `ID_0`, `ID_1`, … in the order the lines appear. Blank
    lines and a lone `>>graph6<<` header line are skipped. -/
@[command_elab loadGraphsFromG6File]
unsafe def loadGraphsFromG6FileImpl : Elab.Command.CommandElab
  | `(load_graphs_from_g6_file $graphName $fileName) => do
    let path := fileName.getString
    let contents ← IO.FS.readFile path
    let mut lineNo : Nat := 0
    let mut count : Nat := 0
    for raw in contents.splitOn "\n" do
      lineNo := lineNo + 1
      let line := raw.trimAscii.toString
      unless line.isEmpty || line == Graph6.header do
        match Graph6.decode line with
        | .error msg => throwError "{path}:{lineNo}: {msg}"
        | .ok data =>
          loadGraphAux (graphName.getId.appendAfter s!"_{count}") (jsonDataOfGraphData data)
          count := count + 1
    if count = 0 then
      logWarning m!"{path} contains no graph6 lines"
    else
      logInfo m!"loaded {count} graphs from {path} as \
                 {graphName.getId.appendAfter "_0"} … {graphName.getId.appendAfter s!"_{count - 1}"}"

  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
