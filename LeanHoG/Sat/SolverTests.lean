import LeanHoG.LoadGraph
import LeanHoG.Tactic
-- Not reachable through `LeanHoG.Tactic`, which pulls in the two Hamiltonian tactic
-- modules but not this one; `Examples.lean` imports it separately for the same reason.
import LeanHoG.Invariant.Bipartite.Tactic

/-!
# Offline end-to-end tests for the certificate-producing commands and tactics

Tests for `#check_traceable`, `#check_hamiltonian`, `#check_hypotraceable`,
`#check_hypohamiltonian`, `#check_bipartite` and their tactic forms, using only graphs
already in the repository: the JSON files in `examples/` and one graph6 string. A SAT
solver on `PATH` is required; network access is not.

`Examples.lean` covers the same commands, but most of its cases use `#download`, so
building it requires network access to houseofgraphs.org.

The cases below reach every outcome of both searches. This includes the graph sizes each
search answers without consulting the solver — 0, 1 and 2 vertices for cycles, 0 for
paths — and the three outcomes of each hypo- search. Also covered: reuse of an existing
certificate declaration when a command is run twice on the same graph, and use of a
tactic inside a named `theorem`, where the certificate may not be registered under the
graph's name.

Each UNSAT case adds an axiom, so building this file emits `added axiom ...` warnings.
-/

namespace LeanHoG.Sat.SolverTests

load_graph G1 "examples/one.json"                 -- 1 vertex, no edges
load_graph Two "examples/two.json"                -- 2 vertices, no edges
load_graph Path1 "examples/path1.json"            -- 2 vertices, one edge
load_graph Path3 "examples/path3.json"            -- 4 vertices in a path
load_graph Cycle7 "examples/cycle7.json"          -- the 7-cycle
load_graph ThreeFour "examples/cycle3-cycle4.json" -- disjoint 3-cycle and 4-cycle
load_graph Cube5 "examples/cube5.json"            -- 32 vertices, bipartite

-- The Petersen graph, in the labelling HoG uses. Loaded from graph6 rather than
-- downloaded, which is the whole point of this file.
load_graph_from_g6 Petersen "IheA@GUAo"

-- The graph on no vertices. `"?"` is `N(0)` followed by an empty adjacency payload;
-- there is no such graph among the JSON files in `examples/`.
load_graph_from_g6 NoVertices "?"

#guard NoVertices.vertexSize = 0

/-! ## Traceability

`searchForHamiltonianPathAux` reaches two outcomes: a path read back from the model, or
an LRAT-checked refutation of the encoding. -/

-- SAT: a Hamiltonian path exists and is registered as an instance.
#check_traceable Cycle7
#check_traceable Path3
#check_traceable Petersen

-- Running the command twice on the same graph must reuse the declaration it already
-- made rather than failing to re-declare it. This is what `hasReusableDecl` is for.
#check_traceable Cycle7

-- UNSAT: no Hamiltonian path. `ThreeFour` is disconnected, `Two` has no edges.
#check_traceable ThreeFour
#check_traceable Two

-- Answered without the solver: on a graph with no vertices `hamiltonianPathCNF` is the
-- empty CNF, which is satisfiable, so a search that consulted the solver here would
-- report a Hamiltonian path in a graph that has no vertices to make one from.
#check_traceable NoVertices   -- `.noVertices`

-- The fact is returned in the same unfolded spelling as the UNSAT case, so it closes a
-- goal stated as `¬ G.traceable` by `assumption` rather than `exact`, as elsewhere.
example : ¬NoVertices.traceable := by check_traceablea NoVertices
example : ¬NoVertices.isHamiltonian := by check_hamiltoniana NoVertices

example : Cycle7.traceable := by check_traceablea Cycle7
example : Path3.traceable := by check_traceablea Path3

-- In the UNSAT direction the hypothesis is the unfolded existential rather than
-- `¬ G.traceable`, which is why `assumption` and not `exact` is the general finisher.
example : ¬ThreeFour.traceable := by check_traceablea ThreeFour

example : ¬ThreeFour.traceable := by
  check_traceable ThreeFour with h
  exact Graph.no_path_not_traceable (h := h)

-- A tactic inside a *named* declaration may only add names beneath its own prefix, so
-- this is the case that `register := false` exists for. It is a separate test from the
-- anonymous `example`s above, and it is the one that used to fail.
theorem two_not_traceable : ¬Two.traceable := by
  check_traceablea Two

/-! ## Hamiltonicity

`searchForHamiltonianCycleAux` reaches five outcomes. Three of them never consult the
solver, because at those sizes the encoding does not answer for `Graph.isHamiltonian` —
see its docstring. All five appear below. -/

#check_hamiltonian Cycle7      -- `.sat`
#check_hamiltonian Path3       -- `.unsat`
#check_hamiltonian ThreeFour   -- `.unsat`, and not for want of a Hamiltonian path
#check_hamiltonian G1          -- `.vacuous`: one vertex is vacuously Hamiltonian
#check_hamiltonian Two         -- `.twoVertices`: never Hamiltonian, encoding says SAT
#check_hamiltonian NoVertices  -- `.noVertices`: no vertex to base a cycle at
#check_hamiltonian Petersen    -- `.unsat`: the standard non-Hamiltonian example

example : Cycle7.isHamiltonian := by check_hamiltoniana Cycle7
example : G1.isHamiltonian := by check_hamiltoniana G1

-- Unlike `check_traceablea` there is no asymmetry here: the hypothesis is
-- `¬ G.isHamiltonian` on the nose, so `exact` works as well as `assumption`.
example : ¬Path3.isHamiltonian := by check_hamiltoniana Path3
example : ¬Two.isHamiltonian := by
  check_hamiltonian Two with h
  exact h

/-! ## Hypohamiltonicity and hypotraceability

Both searches have three outcomes, and all six appear below. The Petersen graph is the
smallest nontrivial hypohamiltonian graph; it is *not* hypotraceable, because it has a
Hamiltonian path. -/

#check_hypohamiltonian Petersen   -- `.hypohamiltonian`
#check_hypohamiltonian Cycle7     -- `.hamiltonian`
#check_hypohamiltonian Path3      -- `.deletionNotHamiltonian`

#check_hypotraceable Petersen     -- `.traceable`
#check_hypotraceable ThreeFour    -- `.deletionNotTraceable`

-- Both hypo- searches are vacuously positive on the graph with no vertices: it has
-- neither a Hamiltonian path nor a Hamiltonian cycle, and there is nothing to delete.
-- Neither is a special case in the tactic; both fall out of the underlying search
-- answering at this size and the deletion loop running zero times.
#check_hypohamiltonian NoVertices -- `.hypohamiltonian`
#check_hypotraceable NoVertices   -- `.hypotraceable`

example : NoVertices.hypotraceable := by check_hypotraceablea NoVertices
example : NoVertices.hypohamiltonian := by check_hypohamiltoniana NoVertices

theorem petersen_hypohamiltonian : Petersen.hypohamiltonian := by
  check_hypohamiltoniana Petersen

-- The positive answer rests on `¬ G.isHamiltonian`, which comes from the solver, so it
-- depends on one unsatisfiability axiom; the cycles in the deletions are actual cycles
-- and cost nothing. If this list ever grows, something has started trusting more.
#print axioms petersen_hypohamiltonian

example : ¬Cycle7.hypohamiltonian := by check_hypohamiltoniana Cycle7

/-! ## Bipartiteness

Not SAT-backed — it is decided by breadth-first search — but it shares the whole
command/tactic scaffolding, so it belongs in the same regression net. -/

#check_bipartite Cube5
#check_bipartite ThreeFour

example : Cube5.bipartite := by check_bipartitea Cube5
example : ¬ThreeFour.bipartite := by check_bipartitea ThreeFour

example : ¬ThreeFour.bipartite := by
  check_bipartite ThreeFour with h
  exact h

end LeanHoG.Sat.SolverTests
