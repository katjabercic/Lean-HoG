import Lean
import Qq
import LeanHoG.Util.Meta
import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.Bipartite.Search

namespace LeanHoG

open Lean Elab Qq

/-- Decide bipartiteness of `graph` by breadth-first search, and return the fact that
    establishes, a proof of it, and which way the answer went.

    `register` says whether the certificate should be backed by a declaration named
    after the graph — the `TwoColoring` instance in the bipartite case, the
    `OddClosedWalk` instance in the other. See `certificateTerm`. -/
unsafe def searchForTwoColoringAux (graphName : Name) (graph : Q(Graph)) (register : Bool) :
    TermElabM (Expr × Expr × Bool) := do
  let G ← Meta.evalExpr' Graph ``Graph graph
  match G.searchBipartite with
  | .error msg => throwError "breadth-first search on {graphName} failed: {msg}"
  | .ok (.twoColoring data) =>
    let certType : Q(Type) := q(TwoColoring $graph)
    let cert ← certificateTerm (certificateName graphName "TwoColoringI") certType
      (TwoColoringOfData graph data) register
    -- Applied to the certificate explicitly, not left to instance synthesis: `mkAppM`
    -- with no arguments returns the bare constant, whose implicit `G` and instance are
    -- still abstracted, and that only fails later in the kernel.
    let proof ← Meta.mkAppOptM ``LeanHoG.TwoColoring.bipartite #[graph, cert]
    return (q(Graph.bipartite $graph), proof, true)
  | .ok (.oddClosedWalk data) =>
    let certType : Q(Type) := q(OddClosedWalk $graph)
    let cert ← certificateTerm (certificateName graphName "OddClosedWalkI") certType
      (OddClosedWalkOfData graph data) register
    let proof ← Meta.mkAppOptM ``LeanHoG.OddClosedWalk.not_bipartite #[graph, cert]
    return (q(¬ Graph.bipartite $graph), proof, false)

------------------------------------------
-- Check bipartiteness command
------------------------------------------

syntax (name := checkBipartite) "#check_bipartite " ident : command
/-- `#check_bipartite G` decides bipartiteness of the graph `G` by breadth-first
    search, and registers a certificate for whichever answer it reaches:

    * **Bipartite.** Coloring each vertex by the parity of its distance from the root of
      its connected component gives a `TwoColoring G` instance.
    * **Not bipartite.** Some edge joins two vertices of equal parity. That edge and the
      two search-tree paths back to their common ancestor close a walk of odd length,
      which gives an `OddClosedWalk G` instance.

    Either instance makes `#eval G.bipartite` return without enumerating all `2^n` maps
    `G.vertex → Fin 2`, which is what deciding bipartiteness on a bare graph does.

    This is the *command* form: it reports what it found. It proves nothing about the
    current goal — see the `check_bipartite` tactic for that. The two are independent:
    the tactic does not require the command to have been run on `G` first.
-/
@[command_elab checkBipartite]
unsafe def checkBipartiteImpl : Command.CommandElab
  | `(#check_bipartite $g) => Command.liftTermElabM do
    let graphName := g.getId
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (_, _, bipartite) ← searchForTwoColoringAux graphName graph (register := true)
    if bipartite then
      logInfo m!"found a two-coloring, registered as \
        {certificateName graphName "TwoColoringI"}"
    else
      logInfo m!"found an odd closed walk, registered as \
        {certificateName graphName "OddClosedWalkI"}"

  | _ => throwUnsupportedSyntax

------------------------------------------
-- Check bipartiteness tactic
------------------------------------------

/-- Run the bipartiteness search on `g` and add what it establishes to the local
    context as a hypothesis named `h` — `g.bipartite` if the search two-colored the
    graph, `¬ g.bipartite` if it found an odd closed walk. Shared by the
    `check_bipartite` and `check_bipartitea` tactics.
-/
unsafe def assertBipartitenessFact (g : Ident) (h : Name) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let graph ← Qq.elabTermEnsuringTypeQ g q(Graph)
    let (type, proof, _) ← searchForTwoColoringAux g.getId graph (register := false)
    Tactic.liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert h type proof
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

syntax (name := checkBipartiteTactic) "check_bipartite " ident (" with" (ppSpace colGt ident))? : tactic
/-- `check_bipartite G` decides bipartiteness of the graph `G` by breadth-first search
    and adds what it decided to the local context as a hypothesis. It serves goals of
    both signs, and you do not have to know which way the answer goes before invoking
    it.

    * **Bipartite.** The hypothesis is `G.bipartite`, proved by the two-coloring the
      search produced.
    * **Not bipartite.** The hypothesis is `¬ G.bipartite`, proved by the odd closed
      walk the search produced.

    Neither depends on an axiom, and neither runs a solver.

    **This tactic adds a hypothesis; it does not close the goal.** Finish with
    `assumption`, or use `check_bipartitea`, which does that for you:

    ```lean
    example : Cycle7.bipartite → False := by
      check_bipartite Cycle7
      intro h; contradiction

    example : Path1.bipartite := by
      check_bipartite Path1
      assumption
    ```

    `check_bipartite G with h` names the hypothesis `h` instead of leaving it
    inaccessible:

    ```lean
    example : ¬Cycle7.bipartite := by
      check_bipartite Cycle7 with h
      exact h
    ```
-/
@[tactic checkBipartiteTactic]
unsafe def checkBipartiteTacticImpl : Tactic.Tactic
  | `(tactic|check_bipartite $g) => assertBipartitenessFact g .anonymous
  | `(tactic|check_bipartite $g with $h) => assertBipartitenessFact g h.getId
  | _ => throwUnsupportedSyntax

syntax (name := checkBipartiteaTactic) "check_bipartitea " ident : tactic
/-- `check_bipartitea G` is `check_bipartite G` followed by `assumption`, in the same
    spirit as `simpa` for `simp`: it derives the fact about bipartiteness of `G` and
    then uses it to close the goal, rather than leaving it in the context. Like
    `check_bipartite`, it decides bipartiteness in both directions:

    ```lean
    example : Path1.bipartite := by
      check_bipartitea Path1

    example : ¬Cycle7.bipartite := by
      check_bipartitea Cycle7
    ```

    Use `check_bipartite` when the derived fact is a step rather than the whole proof.
-/
@[tactic checkBipartiteaTactic]
unsafe def checkBipartiteaTacticImpl : Tactic.Tactic
  | `(tactic|check_bipartitea $g) => do
    assertBipartitenessFact g .anonymous
    Tactic.withMainContext do
      Tactic.liftMetaTactic fun mvarId => do
        try
          mvarId.assumption
          return []
        catch _ =>
          throwError "check_bipartitea derived a fact about bipartiteness of {g}, but it \
            does not close the goal. Use `check_bipartite {g} with h` to name it and \
            finish the proof by hand."

  | _ => throwUnsupportedSyntax

end LeanHoG
