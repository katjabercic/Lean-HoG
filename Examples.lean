import LeanHoG.LoadGraph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Widgets
import LeanHoG.Tactic.SearchDSL
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
#eval Path1.connectedGraph -- should not work, missing certificate
#eval Path1.bipartite

-- The cycle on 7 vertices
load_graph Cycle7 "examples/cycle7.json"
#visualizeGraph Cycle7
#eval Cycle7.bipartite -- works despite missing certificate
#eval Cycle7.connectedGraph

-- The 5-dimensional hypercube from "cube-5.json"
load_graph Cube5 "examples/cube5.json"
#eval Cube5.connectedGraph
#eval Cube5.bipartite

-- The disjoint union of 3- and 4-cycle
load_graph ThreeFour "examples/cycle3-cycle4.json"
#eval ThreeFour.connectedGraph
#eval ThreeFour.numberOfConnectedComponents

-- Load the Petersen graph from the House of Graphs
load_graph Petersen "build/graphs/660.json"
#visualizeGraph Petersen
#eval Petersen.numberOfConnectedComponents

load_graph Foo "build/graphs/670.json"
#visualizeGraph Foo

#compute_hamiltonian_path Foo

#check Foo.HamiltonianPathI

-- #check Foo.HamiltonianPath

-- #eval tryFindHamiltonianPath Foo

-- Search for graphs in the database
-- #search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }

end LeanHoG
