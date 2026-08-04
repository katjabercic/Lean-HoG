import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import Trestle.Solver.Impl.DimacsCommand
import Qq

open Lean Widget Elab Command Term Meta Trestle Qq
namespace LeanHoG

@[widget_module]
def visualize : Widget.Module where
  javascript := include_str ".." / "build" /"js" / "graphVisualization.js"

def Graph.toVisualizationFormat : Graph → Json := fun G =>
  Json.mkObj [
    ("vertexSize", G.vertexSize),
    ("edgeList", Lean.toJson G.edgeSet.toList)
  ]

def HamiltonianPath.toVisualizationFormat (G : Graph) :
  HamiltonianPath G → Json := fun hp =>
  Json.mkObj [
    ("vertexSize", G.vertexSize),
    ("edgeList", Lean.toJson G.edgeSet.toList),
    ("hamiltonianPath", Lean.toJson hp.path.vertices)
  ]

instance widgetInstance : Solver IO := (Solver.Impl.DimacsCommand "kissat")

unsafe def IO.unsafeGet {α} [Inhabited α] (val : IO α) : α := Id.run do
  let .ok val' := unsafeIO val | return default
  return val'

def HamiltonianPath.toVisualizationFormat? (G : Graph) : IO Json := do
  let hp ← tryFindHamiltonianPath G
  match hp with
  | some hp =>
    return Json.mkObj [
      ("vertexSize", G.vertexSize),
      ("edgeList", Lean.toJson G.edgeSet.toList),
      ("hamiltonianPath", Lean.toJson hp.path)
    ]
  | none => return Json.null

/-- Use `#show G` to render a visualization of the graph `G` in the panel widget.
This is done using the `https://js.cytoscape.org/` javascript library. -/
syntax (name := visualizeGraphCmd) "#show " term : command

/-- Use `#visualizeGraph G` to render a visualization of the graph `G` in the panel widget.
This is done using the `https://js.cytoscape.org/` javascript library. -/
@[command_elab visualizeGraphCmd]
def elabVisualizeGraphCmd : CommandElab
  | stx@`(#show $g) => liftTermElabM do
    let wi : Expr ←
      elabWidgetInstanceSpec (← `(widgetInstanceSpec| $(mkIdent ``visualize) with $(← ``((Graph.toVisualizationFormat $g)))))
    let wi : WidgetInstance ← evalWidgetInstance wi
    savePanelWidgetInfo wi.javascriptHash wi.props stx
  | _ => throwUnsupportedSyntax

def buildVisualizationInstance (G : Graph) [inst : HamiltonianPath G] : Json := HamiltonianPath.toVisualizationFormat G inst

syntax (name := visualizeHamiltonianPathCmd) "#show_hamiltonian_path" term : command

@[command_elab visualizeHamiltonianPathCmd]
unsafe def elabVisualizeHamiltonianPathCmd : CommandElab
  | stx@`(#show_hamiltonian_path $G) => liftTermElabM do
    let gg : Expr ← elabTerm G none
    let hpInst ← mkAppM ``HamiltonianPath #[gg]
    if let .some _ ← synthInstance? hpInst then
      let vizf ← ``((Graph.toVisualizationFormat $G))
      let wis ← `(Widget.widgetInstanceSpec| $(mkIdent ``visualize) with $vizf)
      let wi : Expr ← Widget.elabWidgetInstanceSpec wis
      let wi ← Widget.evalWidgetInstance wi
      savePanelWidgetInfo wi.javascriptHash wi.props stx
    else
      IO.println "Hamiltonian path for graph not found."

  | _ => throwUnsupportedSyntax


end LeanHoG
