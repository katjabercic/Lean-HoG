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

import Lean.Elab.Command

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

unsafe def loadGraphObject (graphName : Name) (jsonData : JSONData) : Elab.Command.CommandElabM Graph := do
  loadGraphAux graphName jsonData
  Lean.evalConst Graph graphName

unsafe def convertGraph  (graphName : Lean.Name) (jsonData : JSONData) : IO Graph := do
      let elabGraph : Elab.Command.CommandElabM Graph := loadGraphObject graphName jsonData
      let graph : CoreM Graph := liftCommandElabM (elabGraph)
      let env ← importModules #[{module := "LeanHoG"}] Options.empty
      have context : Core.Context := {fileName := "LoadGraph.lean", fileMap := default}
      have state : Core.State := {env := env}
      Prod.fst <$> (graph.toIO context state)

unsafe def readGraph (graphName : Lean.Name) (path : System.FilePath) : IO Graph := do
    let jsonData ← loadJSONData JSONData path
    convertGraph graphName jsonData

/-- `load_graph <ID> <file>` loads a graph into the given Lean identifier `ID` from the given file. -/
@[command_elab loadGraph]
unsafe def loadGraphImpl : Elab.Command.CommandElab
  | `(load_graph $graphName $fileName) => do
    let graphName := graphName.getId
    let jsonData ← loadJSONData JSONData fileName.getString
    loadGraphAux graphName jsonData

  | _ => Elab.throwUnsupportedSyntax

/-- Checks the graph invariant against what is stored in HoG and outputs an error message in case of an error.
Params:
   propType: the expected type for the check (e.g., number of vertices = hog.number of vertices)
   propValue: the expression to type check
   graphName: the name of the graph
   propKeyword: a keyword to append to the graphName to build the name of the expression.
   propName: the name of the property (used in the error message).
-/
unsafe def tryCheck (propType : Expr) (propValue : Expr) (graphName : Name) (propKeyword : String) (propName : String) : Elab.Command.CommandElabM Unit := do
      let checkName := Name.mkStr graphName propKeyword
      -- We can use try catch to catch errors and use our own error messages.
      try Elab.Command.liftCoreM <| addAndCompile <| .defnDecl {
        name := checkName
        levelParams := []
        type := propType
        value := propValue
        hints := .regular 0
        safety := .safe
      }
      catch _ => logError s!"Error when checking {propName} for graph {graphName}."


/-- Checks that a given graph has the right values for the different invariants in HoG. Only works if we have the invariant from HoG and if we have a valid certificate for this invariant. -/
unsafe def checkHoGGraphAux (graph : Q(Graph)) (graphName : Name) : Elab.Command.CommandElabM Unit := do
  -- Because the instances might not exist, we first need to look for them
  if let .some (rawHoGInstance : Q(RawHoG $graph)) ← (Elab.Command.liftTermElabM <| Meta.trySynthInstance q(RawHoG $graph) .none) then
    if let .some (conCompsInstance : Q(ConnectedComponents $graph)) ← (Elab.Command.liftTermElabM <| Meta.trySynthInstance q(ConnectedComponents $graph) .none) then
      -- The idea is to try to build a "theorem" and type check it.
      -- For some reason, it does not work using the existing "check" functions. Maybe I was doing it wrong.
      have compsCheck : Q(decide (($rawHoGInstance).numberOfComponents? = .some ($conCompsInstance).val) = true) := (q(Eq.refl true) : Lean.Expr)
      tryCheck
        q(($rawHoGInstance).numberOfComponents? = ($conCompsInstance).val)
        q(of_decide_eq_true $compsCheck)
        graphName
        "connComps"
        "number of connected components"
    -- For bipartiteness, we should not check unless we have one of the two certificates. The default bipartite check will quickly fill the memory if we try too many graphs.
    if let .some (_ : Q(TwoColoring $graph)) ← (Elab.Command.liftTermElabM <| Meta.trySynthInstance q(TwoColoring $graph) .none) then
      have bipCheck : Q(decide (($rawHoGInstance).bipartite? = .some true) = true) := (q(Eq.refl true) : Lean.Expr)
      tryCheck
        q(($rawHoGInstance).bipartite? = .some true)
        q(of_decide_eq_true $bipCheck)
        graphName
        "bip"
        "bipartiteness"
    if let .some (_ : Q(OddClosedWalk $graph)) ← (Elab.Command.liftTermElabM <| Meta.trySynthInstance q(OddClosedWalk $graph) .none) then
      have bipCheck : Q(decide (($rawHoGInstance).bipartite? = .some false) = true) := (q(Eq.refl true) : Lean.Expr)
      tryCheck
        q(($rawHoGInstance).bipartite? = .some false)
        q(of_decide_eq_true $bipCheck)
        graphName
        "bip"
        "bipartiteness"

/-- This command takes the graph identifier as input. -/
syntax (name := checkHoGGraph) "check_hog_graph" ident : command

@[command_elab checkHoGGraph]
unsafe def checkCowImpl : Elab.Command.CommandElab
  | `(check_hog_graph $graph) => do
    -- We need the quoted graph associated with the given constant.
    let graphQ : Q(Graph) := Lean.mkConst graph.getId
    checkHoGGraphAux graphQ graph.getId
  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
