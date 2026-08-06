import LeanHoG.LoadGraph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Widgets
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Basic
import LeanHoG.Invariant.HamiltonianPath.Tactic

namespace LeanHoG

-- You may have to change this
set_option leanHoG.pythonExecutable "python"


-- Loading graphs, visualizing them, and checking their properties

-- In the examples, some invariant certificates are omitted on purpose.
-- Below, they are marked with a comment.

-- The discrete graph on two vertices
load_graph Two "examples/two.json"
#eval Two.connectedGraph
#eval Two.connected 0 1
#eval Two.numberOfConnectedComponents

-- The path of length 1 (on two vertices)
load_graph Path1 "examples/path1.json"
#eval Path1.connectedGraph
#eval Path1.bipartite

-- The cycle on 7 vertices
load_graph Cycle7 "examples/cycle7.json"
#show Cycle7
#eval Cycle7.bipartite -- works despite missing certificate
#eval Cycle7.connectedGraph

-- The 5-dimensional hypercube from "cube-5.json"
load_graph Cube5 "examples/cube5.json"
#eval Cube5.connectedGraph
-- #eval Cube5.bipartite

-- The disjoint union of 3- and 4-cycle
load_graph ThreeFour "examples/cycle3-cycle4.json"
#eval ThreeFour.connectedGraph
#eval ThreeFour.numberOfConnectedComponents


-- Checking bipartiteness with and without certificates

-- The next three graphs have 15, 16 and 16 vertices, and their JSON carries neither
-- a two-coloring nor an odd closed walk. Deciding bipartiteness therefore searches
-- the 2^15 and 2^16 maps from vertices to `Fin 2` for a proper one. Poussin and
-- Hanoi have none; the 4-dimensional hypercube does.
load_graph PoussinNoCertificates "examples/Poussin-no-certificates.json"
#eval PoussinNoCertificates.bipartite
load_graph HanoiNoCertificates "examples/Hanoi2Disks-no-certificates.json"
#eval HanoiNoCertificates.bipartite
load_graph Cube4NoCertificates "examples/cube4-no-certificates.json"
#eval Cube4NoCertificates.bipartite

-- The same two graphs with certificates. Each carries an odd closed walk, which
-- decides bipartiteness with no search.
load_graph Poussin "examples/Poussin.json"
#eval Poussin.bipartite
load_graph Hanoi "examples/Hanoi2Disks.json"
#eval Hanoi.bipartite


-- Loading and searching for graphs from the House of Graphs

-- Load the Petersen graph from HoG
-- First run `lake exe download 660`
#download Petersen 660
#show Petersen
#eval Petersen.numberOfConnectedComponents
#eval Petersen.g6

-- Alternatively, download graphs directly from HoG
#download Wheel 204
#check Wheel
#show Wheel
#eval Wheel.g6

-- Search the HoG database directly from Lean
#search_hog hog{ bipartite = true ∧ (numberOfEdges = 2 ∨ numberOfVertices < 6) }
load_graph hog_904 "build/graphs/904.json"
#show hog_904
-- Uncomment the line below to initiate the search
-- #search_hog hog{ traceable = true ∧ numberOfVertices > 3 ∧ minimumDegree < numberOfVertices / 2}

-----------------------------------------
-- Hamiltonian paths
-----------------------------------------

-- We can use a command to compute a Hamiltonian path and add it as an instance
#check_traceable Wheel
#show_hamiltonian_path Wheel

-- We can also show that there is no Hamiltonian path is some graphs
#search_hog hog{ traceable = false ∧ numberOfEdges = 2}
load_graph hog_896 "build/graphs/896.json"
#show hog_896
#eval hog_896.g6
#check_traceable hog_896
#show_hamiltonian_path hog_896

-- The command only reports what it found. To use the result in a proof there is
-- a tactic of the same name, without the leading `#`. It decides traceability in
-- both directions, so it proves that a graph *is* traceable just as well as that
-- it is not.

-- `check_traceable` adds the fact it derives to the context as a hypothesis; it
-- does not close the goal, so the proof is finished with `assumption`.
#download Fork 30
example : ¬Fork.traceable := by
  check_traceable Fork
  assumption

-- The same tactic on a goal of the opposite sign. Here the solver returns a
-- satisfying assignment, which is read back as an actual Hamiltonian path, so the
-- hypothesis is `Petersen.traceable` and the proof depends on no axiom.
example : Petersen.traceable := by
  check_traceable Petersen
  assumption

-- `with h` gives that hypothesis a name instead of leaving it inaccessible. In the
-- UNSAT case the hypothesis is the unfolded existential rather than `¬ G.traceable`,
-- which is why `assumption` above is the finisher to reach for in general.
#download HGraph 334
example : ¬HGraph.traceable := by
  check_traceable HGraph with h
  exact h

-- `check_traceablea` performs the `assumption` step itself, in the same spirit as
-- `simpa` for `simp`.
#download Cross 208
example : ¬Cross.traceable := by
  check_traceablea Cross

-- `#check_traceable Wheel` above already registered a Hamiltonian path for `Wheel`.
-- The tactic reuses that certificate rather than clashing with it.
example : Wheel.traceable := by
  check_traceablea Wheel

---------------------------------------
-- Tactics
---------------------------------------

-- Tactic to close goals of the form ∃ G, P G
-- Not all P are supported, only propositions using invariants defined
-- Note: To check for Hamiltonian paths, we use a SAT solver.
-- If the solver says the problem is unsat, we check its proof with the
-- verified LRAT checker from `Std`.
-- For this you need to have a solver installed, capable of producing
-- LRAT proofs of unsat. We recommend CaDiCal 1.9.5+ (https://github.com/arminbiere/cadical).
-- We set the location of the solver with the user option `leanHoG.solverCmd`.
-- Uncomment the line below to run the tactic

-- set_option leanHoG.solverCmd "cadical"
example : ∃ (G : Graph), G.traceable ∧ G.vertexSize > 3 ∧ (G.minimumDegree < G.vertexSize / 2) := by
  find_example

-------------------------------------------------------------------
-- Capstone: traceability is not determined by the degree sequence
-------------------------------------------------------------------

-- Most of the classical sufficient conditions for traceability read nothing but
-- the degree sequence: Dirac's `δ(G) ≥ (n-1)/2`, Ore's condition, Chvátal's
-- condition. None of them can be sharpened into a characterisation, because the
-- degree sequence does not determine traceability at all. Two graphs from HoG
-- witness that, and they agree on a good deal more than their degrees.
--
-- Both have 7 vertices, 11 edges, degree sequence (5,5,3,3,2,2,2), independence
-- number 4, vertex connectivity 2 and girth 3, and neither is bipartite. HoG
-- records one of them as traceable and the other as not. The names below
-- deliberately do not say which is which: `check_traceable` decides that.
--
-- The difference is not something one spots by looking, either. Both graphs have
-- exactly two vertices of degree 5. Deleting that pair from `Twin2` leaves four
-- components, {0}, {1}, {2} and {3,4}; deleting it from `Twin1` leaves three,
-- {0}, {1} and {2,3,4}. Removing two vertices from a Hamiltonian path can leave
-- at most three pieces, so `Twin2` has no Hamiltonian path. The obstruction sits
-- in the scattering number, and no condition on degrees can see it.

#download Twin1 56172
#download Twin2 56196
#show Twin1
#show Twin2

#eval Twin1.degreeSequence
#eval Twin2.degreeSequence

section Capstone

-- Deciding `¬ G.bipartite` with no certificate to hand searches for a
-- two-colouring, which overruns the default recursion budget.
set_option maxRecDepth 10000

/-- Traceability is not a function of the degree sequence: there are two
    connected, non-bipartite graphs with the same degree sequence, one of which
    is traceable and one of which is not. -/
theorem traceability_not_determined_by_degree_sequence :
    ∃ (G H : Graph),
      G.degreeSequence = H.degreeSequence ∧
      G.connectedGraph ∧ H.connectedGraph ∧
      ¬ G.bipartite ∧ ¬ H.bipartite ∧
      G.traceable ∧ ¬ H.traceable := by
  refine ⟨Twin1, Twin2, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · check_traceablea Twin1
  · check_traceablea Twin2

end Capstone

-- What the theorem rests on. `Twin1.traceable` is witnessed by the path the
-- solver returned, so the positive half contributes no axiom. The negative half
-- does, and it is exactly the unsatisfiability of the encoding of `Twin2` — the
-- one claim in the proof that comes from the solver rather than from Lean, and
-- the LRAT checker has accepted its proof. It is named beneath the theorem
-- because that is where a tactic is allowed to put a declaration.
#print axioms traceability_not_determined_by_degree_sequence

end LeanHoG
