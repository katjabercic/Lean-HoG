import Lean
import Qq
import Aesop.Util.Basic
import Std.Data.List.Basic

import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Tactic.ParseExpr
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.Tactic
import LeanHoG.Invariant.HamiltonianCycle.Tactic

namespace LeanHoG

-----------------------------------------------------------------
-- Download graph command
-----------------------------------------------------------------

syntax (name := downloadHoG) "#download" ident ppSpace term : command

open Lean Qq in
/-- `#download <name> <hog_id>` downloads the graphs with House of Graphs
    ID `<hog_id>` and loads it into the veriable `<name>`.

    Note: The graph is downloaded into the folder defined by the user option
    `leanHoG.graphDownloadLocation`.

    Note: To download the graph it uses an external python script. The location
    of the python executable is provided by the user option `leanHoG.pythonExecutable`.

    Note: The python environment is expected to have the `requests` library installed.
 -/
@[command_elab downloadHoG]
unsafe def downloadHoGImpl : Elab.Command.CommandElab
  | `(#download $name $id) =>  do
    let n ← Elab.Command.liftTermElabM do
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

  | _ => Elab.throwUnsupportedSyntax

-----------------------------------------------------------------
-- Search tactic
-----------------------------------------------------------------

syntax (name := findExample) "find_example" : tactic

open Lean Qq Elab Tactic in
/-- `find_example` works on goals of the form `∃ (G : Graph), P G`, where
    `P` is a limited propositional formula on `G` which consists of conjunction,
    disjunctions and comparisons of invariants of G, i.e. the kinds of queries
    HoG is able to answer.

    Note: The tactic constructs a query and sends it to the HoG database.

    Example goal the tactic works on:
    `∃ (G : Graph), G.traceable ∧ G.vertexSize > 3 ∧ (G.minimumDegree < G.vertexSize / 2)`
-/
@[tactic findExample]
unsafe def findExampleImpl : Tactic.Tactic
  | stx@`(tactic|find_example) =>
    Tactic.withMainContext do
      let goal ← Tactic.getMainGoal
      let goalDecl ← goal.getDecl
      let goalType := goalDecl.type
      let graphType : Expr ← Term.mkConst ``Graph
      let exists_intro ← Term.mkConst ``Exists.intro
      try
        let enqs ← decomposeExistsQ goalType
        let mentionsTracability := enqs.any (fun enq => enq.mentionsBoolInv .Traceable)
        let mentionsHamiltonicity := enqs.any (fun enq => enq.mentionsBoolInv .Hamiltonian)
        let hash := hash enqs
        let query := HoGQuery.build enqs
        let graphs ← liftCommandElabM (queryDatabaseForExamplesAux [query] hash)
        if h : graphs.length > 0 then
          -- We now have to load one of the results into the context
          -- TODO: Currently we globaly load the graph, should just load it into the local context
          let ⟨graphId⟩ := graphs[0]'(by simp_all only [not_lt_zero'])
          let opts ← getOptions
          let downloadLocation := opts.get leanHoG.graphDownloadLocation.name leanHoG.graphDownloadLocation.defValue
          let graphLoc := System.mkFilePath [downloadLocation, s!"{graphId}.json"]
          let graphIdent := mkIdent (Name.mkSimple s!"hog_{graphId}")
          let jsonData ← loadJSONData JSONData graphLoc
          liftCommandElabM (loadGraphAux graphIdent.getId jsonData)

          -- Now try to use the loaded graph to close the goal
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
                let r ← Lean.Elab.Tactic.elabTermEnsuringType graphIdent goalType
                goal.assign r
                -- Now try to simp which will among other things look for instance for e.g. HamiltonianPath
                if mentionsTracability then
                  -- If we want to prove things about tracability we need to search for a Hamiltonian path
                  checkTraceableTacticAux graphIdent.getId r .anonymous
                if mentionsHamiltonicity then
                  checkHamiltonianTacticAux graphIdent.getId r .anonymous
                let ctx ← mkSimpContext (← `(tactic|simp_all [LeanHoG.Graph.no_path_not_traceable, not_false_eq_true])) false
                let (result?, _) ← Meta.simpAll (← getMainGoal) ctx.ctx (simprocs := ctx.simprocs)
                match result? with
                | none => replaceMainGoal []
                | some mvarId =>
                  replaceMainGoal [mvarId]
                  Tactic.evalDecide stx
                Lean.logInfo s!"Closed goal using {graphIdent.getId}"
              -- Visualize the graph we used to close the goal
              -- TODO: Make this an option
              let wi : Expr ←
                Widget.elabWidgetInstanceSpecAux (mkIdent `visualize) (← ``((Graph.toVisualizationFormat $graphIdent)))
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
