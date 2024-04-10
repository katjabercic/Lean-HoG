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

-- The next two graphs have respectively 15 and 16 edges.
-- Uncomment the next lines to see the time Lean needs to decide bipartitness without a certificate
-- load_graph PoussinNoCertificates "examples/Poussin-no-certificates.json"
-- #eval PoussinNoCertificates.bipartite
-- load_graph HanoiNoCertificates "examples/Hanoi2Disks-no-certificates.json"
-- #eval HanoiNoCertificates.bipartite

-- Using a certificate provides a significant speed up.
load_graph Poussin "examples/Poussin.json"
-- #eval Poussin.bipartite
load_graph Hanoi "examples/Hanoi2Disks.json"
-- #eval Hanoi.bipartite


-- Loading and searching for graphs from the House of Graphs

-- Load the Petersen graph from HoG
-- First run `lake exe download 660`
#download Petersen 660
#show Petersen
#eval Petersen.numberOfConnectedComponents

-- Alternatively, download graphs directly from HoG
#download Wheel 204
#check Wheel
#show Wheel

-- Search the HoG database directly from Lean
#search hog{ bipartite = true ∧ (numberOfEdges = 2 ∨ numberOfVertices < 6) }
load_graph hog_904 "build/graphs/904.json"
#show hog_904
-- Uncomment the line below to initiate the search
-- #search hog{ traceable = true ∧ numberOfVertices > 3 ∧ minimumDegree < numberOfVertices / 2}


-- Hamiltonian paths

-- We can use a command to compute a Hamiltonian path and add it as an instance
#check_traceable Wheel
#show_hamiltonian_path Wheel

-- Tactic to close goals of the form ∃ G, P G
-- Not all P are supported, only propositions using invariants defined
-- Note: To check for Hamiltonian paths, we use a SAT solver.
-- If the solver says the problem is unsat, we check it's proof with a
-- verified proof checker.
-- For this you need to have a solver installed, capable of producing
-- LRAT proofs of unsat. We recommend CaDiCal 1.9.5+ (https://github.com/arminbiere/cadical)
-- and cake_lpr (https://github.com/tanyongkiam/cake_lpr).
-- We set the location of the solver and proof checker with user options
-- `leanHoG.solverCmd` and `leanHoG.proofCheckerCmd`.
-- Uncomment lines below to run the tactic

-- set_option leanHoG.solverCmd "cadical"
-- set_option leanHoG.proofCheckerCmd "cake_lpr"
-- example : ∃ (G : Graph), G.isTraceable ∧ G.vertexSize > 3 ∧ (G.minimumDegree < G.vertexSize / 2) := by
-- find_example

end LeanHoG
