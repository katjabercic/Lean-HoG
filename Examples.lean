import LeanHoG.LoadGraph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Widgets
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Basic
import LeanHoG.Invariant.HamiltonianPath.Tactic

namespace LeanHoG

-- Loading graphs, visualizing them, and checking their properties

/-
In the examples, some invariant certificates are omitted on purpose.
Below, they are marked with a comment. In some cases, the kernel can
compute the invariant values, but not in all of them.
-/

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
#visualizeGraph Cycle7
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

-- The next two graphs have respectively 15 and 16 edges.
-- Uncomment the next lines to see the time Lean needs to decide bipartitness without a certificate
/-
load_graph PoussinNoCertificates "examples/Poussin-no-certificates.json"
#eval PoussinNoCertificates.bipartite
-/

/-
load_graph HanoiNoCertificates "examples/Hanoi2Disks-no-certificates.json"
#eval HanoiNoCertificates.bipartite
-/

-- Using a certificate provides a significant speed up.
load_graph Poussin "examples/Poussin.json"
-- #eval Poussin.bipartite

load_graph Hanoi "examples/Hanoi2Disks.json"
-- #eval Hanoi.bipartite

-- Load the Petersen graph from the House of Graphs
load_graph Petersen "build/graphs/660.json"
#visualizeGraph Petersen
#eval Petersen.numberOfConnectedComponents

-- We can download graphs directly from HoG
#download_hog_graph Wheel 204
#check Wheel
#visualizeGraph Wheel

-- We can use a command to compute a Hamiltonian path and add it as an instance

-- #compute_hamiltonian_path Wheel
-- #check Wheel.HamiltonianPathI

-- Search the HoG database directly from Lean
-- Uncomment the line below to initiate the search
-- #search_hog hog{ bipartite = true ∧ (numberOfEdges = 2 ∨ numberOfVertices < 6) }

-- Tactic to close goals of the form ∃ G, P G
-- Not all P are supported, only propositions using invariants defined
-- Note: To check for Hamiltonian paths, we use a SAT solver.
-- If the solver says the problem is unsat, we check it's proof with a
-- verified proof checker.
-- For this you need to have a solver installed, capable of producing
-- LRAT proofs of unsat. We recommend CaDiCal 1.9.5+ (https://github.com/arminbiere/cadical)
-- and cake_lpr (https://github.com/tanyongkiam/cake_lpr).
-- We set the location of the solver and proof checker with user options
-- `leanHoG.solverCmd` and `leanHoG.cake_lprCmd`.
-- Uncomment lines below to run the tactic

-- set_option leanHoG.solverCmd "cadical"
-- set_option leanHoG.cake_lprCmd "cake_lpr"
-- example : ∃ (G : Graph), G.isTraceable ∧ G.vertexSize > 3 ∧ (G.minimumDegree < G.vertexSize / 2) := by
--   search_for_example

end LeanHoG
