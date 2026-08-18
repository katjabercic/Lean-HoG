import Lean
import Qq
import Aesop.Util.Basic

import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Tactic.ParseExpr
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Invariant.HamiltonianPath.Tactic
import LeanHoG.Invariant.HamiltonianCycle.Basic
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
    let downloadGraphPy := packageDirPath / "Download" / "downloadGraph.py"
    let output ← IO.Process.output {
      cmd := pythonExe
      args := #[s!"{downloadGraphPy}", downloadLocation, s!"{n}"]
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
        let mentionsTracability := enqs.any (fun enq => enq.mentionsTracability)
        let mentionsHamiltonicity := enqs.any (fun enq => enq.mentionsHamiltonicity)
        let hash := hash enqs
        let query := HoGQuery.build enqs
        let graphs ← liftCommandElabM (queryDatabaseForExamplesAux [query] hash)
        if h : graphs.length > 0 then
          -- We now have to load one of the results into the context
          -- TODO: Currently we globaly load the graph, should just load it into the local context
          let ⟨graphId⟩ := graphs[0]'(by simp_all only [])
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
                -- HoG has answered the query, but its answer is data: for the invariants
                -- Lean cannot compute it needs a certificate of its own, found with a SAT
                -- solver. Traceability needs a Hamiltonian path, Hamiltonicity a Hamiltonian
                -- cycle. Collect what each search establishes, then let `simp_all`/`decide`
                -- close what is left of the goal.
                let mut facts : Array (Expr × Expr) := #[]
                if mentionsTracability then
                  -- `register := true`: in the SAT case the goal is closed by instance
                  -- synthesis rather than from the proof term, so the certificate has to be
                  -- a registered instance and not just a term — which is also why only the
                  -- UNSAT fact is asserted here. That fact is the unfolded existential;
                  -- `no_path_not_traceable` below is what turns it into `¬ G.traceable`.
                  let (type, proof, res) ← LeanHoG.searchForHamiltonianPathAux graphIdent.getId r
                    (register := true)
                  match res with
                  | .unsat | .noVertices => facts := facts.push (type, proof)
                  | .sat => pure ()
                if mentionsHamiltonicity then
                  -- Every outcome of the cycle search names the fact it established
                  -- (`Graph.isHamiltonian` or its negation) and returns a proof of it, so
                  -- there is nothing to bridge and no need to go through synthesis. Note the
                  -- two degenerate sizes never reach the solver — see
                  -- `searchForHamiltonianCycleAux`.
                  let (type, proof, _) ← LeanHoG.searchForHamiltonianCycleAux graphIdent.getId r
                    (register := true)
                  facts := facts.push (type, proof)
                for (type, proof) in facts do
                  Tactic.liftMetaTactic fun mvarId => do
                    let mvarIdNew ← mvarId.assert .anonymous type proof
                    let (_, mvarIdNew) ← mvarIdNew.intro1P
                    return [mvarIdNew]
                -- `no_path_not_traceable` bridges the path search's UNSAT fact to
                -- `¬ G.traceable`, and `isNonHamiltonian` unfolds the goal's spelling of
                -- non-Hamiltonicity to the `¬ G.isHamiltonian` the cycle search returns.
                let closing ←
                  if mentionsTracability || mentionsHamiltonicity then
                    `(tactic|simp_all only [LeanHoG.Graph.no_path_not_traceable,
                      LeanHoG.Graph.isNonHamiltonian, not_false_eq_true])
                  else
                    `(tactic|simp_all)
                let ctx ← mkSimpContext closing false
                let (result?, _) ← Meta.simpAll (← getMainGoal) ctx.ctx (simprocs := ctx.simprocs)
                match result? with
                | none => replaceMainGoal []
                | some mvarId =>
                  replaceMainGoal [mvarId]
                  Tactic.evalDecide stx
                Lean.logInfo s!"Closed goal using {graphIdent.getId}"
              -- Visualize the graph we used to close the goal
              -- TODO: Make this an option
              let vizf ← ``((Graph.toVisualizationFormat $graphIdent))
              let wis ← `(Widget.widgetInstanceSpec| $(mkIdent ``visualize) with $vizf)
              let wi : Expr ← Widget.elabWidgetInstanceSpec wis
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
