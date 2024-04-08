import Lean
import Qq
import Aesop.Util.Basic
import Std.Data.List.Basic

import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Tactic.ParseExpr
import LeanHoG.Invariant.HamiltonianPath.Basic

namespace LeanHoG

-----------------------------------------------------------------
-- Download graph command
-----------------------------------------------------------------

syntax (name := downloadHoGGraph) "#download_hog_graph " ident ppSpace term : command

open Lean Qq Elab in
/-- `#download_hog_graph <name> <hog_id>` downloads the graphs with House of Graphs
    ID `<hog_id>` and loads it into the veriable `<name>`.

    Note: The graph is downloaded into the folder defined by the user option
    `leanHoG.graphDownloadLocation`.

    Note: To download the graph it uses an external python script. The location
    of the python executable is provided by the user option `leanHoG.pythonExecutable`.

    Note: The python environment is expected to have the `requests` library installed.
 -/
@[command_elab downloadHoGGraph]
unsafe def downloadHoGGraphImpl : Command.CommandElab
  | `(#download_hog_graph $name $id) =>  do
    let n ← Command.liftTermElabM do
      let qn : Q(Nat) ← (elabTermEnsuringTypeQ id q(Nat))
      evaluateNat qn
    let opts ← getOptions
    let pythonExe := opts.get leanHoG.pythonExecutable.name leanHoG.pythonExecutable.defValue
    let downloadLocation := opts.get leanHoG.graphDownloadLocation.name leanHoG.graphDownloadLocation.defValue
    let output ← IO.Process.output {
      cmd := pythonExe
      args := #["Download/downloadGraph.py", downloadLocation, s!"{n}"]
    }
    if output.exitCode ≠ 0 then
      throwError f!"failed to download graph: {output.stderr}"
    let filePath := s!"{downloadLocation}/{n}.json"
    let jsonData ← loadJSONData JSONData filePath
    loadGraphAux name.getId jsonData
    logInfo s!"loaded graph hog_{n} into {name.getId}"

  | _ => throwUnsupportedSyntax

-----------------------------------------------------------------
-- Search tactic
-----------------------------------------------------------------

syntax (name := searchForExampleInHoG) "search_for_example" : tactic

open Lean Qq Elab in
@[tactic searchForExampleInHoG]
unsafe def searchForExampleInHoGImpl : Tactic.Tactic
  | stx@`(tactic|search_for_example) =>
    Tactic.withMainContext do
      let goal ← Tactic.getMainGoal
      let goalDecl ← goal.getDecl
      let goalType := goalDecl.type
      let graphType : Expr ← Term.mkConst ``Graph
      let exists_intro ← Term.mkConst ``Exists.intro
      try
        let enqs ← decomposeExistsQ goalType
        let hash := hash enqs
        let query := HoGQuery.build enqs
        let graphs ← liftCommandElabM (queryDatabaseForExamples [query] hash)
        if h : graphs.length > 0 then
          let ⟨graphId⟩ := graphs[0]'(by simp_all only [not_lt_zero'])
          -- IO.println f!"Found such a graph: {name}"
          let mvarIds' ← Lean.MVarId.apply goal exists_intro
          Tactic.replaceMainGoal mvarIds'
          let newGoals ← Tactic.getGoals
          for goal in newGoals do
            -- find the goal with type Graph and try to close it with `graph`
            let goalDecl ← goal.getDecl
            let goalType := goalDecl.type
            if ← Meta.isDefEq goalType graphType then
              -- check that the goal is not already assigned
              goal.checkNotAssigned `search_for_counterexample
              -- try to close the goal with the found graph
              goal.withContext do
                let r ← Lean.Elab.Tactic.elabTermEnsuringType graphId goalType
                goal.assign r
              -- Now try to simp which will among other things look for instance for e.g. HamiltonianPath
              Tactic.evalSimp stx
              Tactic.evalDecide stx
              Lean.logInfo s!"Closed goal using {graphId.getId}"
              -- Visualize the graph we used to close the goal
              -- TODO: Make this an option
              let wi : Expr ←
                Widget.elabWidgetInstanceSpecAux (mkIdent `visualize) (← ``((Graph.toVisualizationFormat $graphId)))
              let wi ← Widget.evalWidgetInstance wi
              Widget.savePanelWidgetInfo wi.javascriptHash wi.props stx
            else
              continue
        else
          throwError "Could not find any graphs matching criteria"

      catch e =>
        throwError m!"search failed: {e.toMessageData}"

  | _ => throwUnsupportedSyntax

end LeanHoG
