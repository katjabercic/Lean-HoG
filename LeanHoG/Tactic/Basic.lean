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

open Lean Widget Elab Term Tactic Command Qq


-----------------------------------------------------------------
-- Download graph command
-----------------------------------------------------------------

syntax (name := downloadHoGGraph) "#download_hog_graph " term : command

@[command_elab downloadHoGGraph]
unsafe def downloadHoGGraphImpl : CommandElab
  | `(#download_hog_graph $id) => liftTermElabM do
    let qn : Q(Nat) ← elabTermEnsuringTypeQ id q(Nat)
    let n ← evaluateNat qn
    let opts ← getOptions
    let pythonExe := opts.get leanHoG.pythonExecutable.name leanHoG.pythonExecutable.defValue
    let downloadLocation := opts.get leanHoG.graphDownloadLocation.name leanHoG.graphDownloadLocation.defValue
    let output ← IO.Process.output {
      cmd := pythonExe
      args := #["Download/downloadGraph.py", downloadLocation, s!"{n}", s!"{n}"]
    }
    if output.exitCode ≠ 0 then
      throwError f!"failed to download graph: {output.stderr}"
    logInfo s!"downloaded graph to {downloadLocation}/{n}.json"

  | _ => throwUnsupportedSyntax


-----------------------------------------------------------------
-- Search tactic
-----------------------------------------------------------------

syntax (name := searchForExampleInHoG) "search_for_example" : tactic

@[tactic searchForExampleInHoG]
unsafe def searchForExampleInHoGImpl : Tactic
  | stx@`(tactic|search_for_example) =>
    withMainContext do
      let goal ← getMainGoal
      let goalDecl ← goal.getDecl
      let goalType := goalDecl.type
      let graphType : Expr ← mkConst ``Graph
      let exists_intro ← mkConst ``Exists.intro
      try
        let enqs ← decomposeExistsQ goalType
        let hash := hash enqs
        let query := HoGQuery.build enqs
        let graphs ← liftCommandElabM (queryDatabaseForExamples [query] hash)
        if h : graphs.length > 0 then
          let ⟨graphId⟩ := graphs[0]'(by simp_all only [not_lt_zero'])
          -- IO.println f!"Found such a graph: {name}"
          let mvarIds' ← Lean.MVarId.apply goal exists_intro
          replaceMainGoal mvarIds'
          let newGoals ← getGoals
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
              evalSimp stx
              evalDecide stx
              Lean.logInfo s!"Closed goal using {graphId.getId}"
              -- Visualize the graph we used to close the goal
              -- TODO: Make this an option
              let wi : Expr ←
                elabWidgetInstanceSpecAux (mkIdent `visualize) (← ``((Graph.toVisualizationFormat $graphId)))
              let wi : WidgetInstance ← evalWidgetInstance wi
              savePanelWidgetInfo wi.javascriptHash wi.props stx
            else
              continue
        else
          throwError "Could not find any graphs matching criteria"

      catch e =>
        throwError m!"search failed: {e.toMessageData}"

  | _ => throwUnsupportedSyntax

end LeanHoG
