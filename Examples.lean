import LeanHoG.LoadGraph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Widgets
import LeanHoG.Tactic.SearchDSL

namespace LeanHoG

-- Load the cycle on 7 vertices from JSON file
load_graph Cycle7 "examples/cycle7.json"

#visualizeGraph Cycle7

-- Check that Cycle7 is connected
#eval Cycle7.is_connected
#eval Cycle7.numberOfConnectedComponents

-- Load the K_{2,2,2,2,2} from "cube-5.json"
load_graph Cube5 "examples/cube5.json"

-- Check that Cube5 is connected
#eval Cube5.is_connected

-- Load the disjoint union of 3- and 4-cycle
load_graph Cow "examples/cycle3-cycle4.json"
#eval Cow.is_connected
#eval Cow.numberOfConnectedComponents

-- Discrete graph on two points
load_graph Two "examples/two.json"
#eval Two.numberOfConnectedComponents

-- Load the Petersen graph from the House of Graphs
load_graph Petersen "build/graphs/660.json"
#visualizeGraph Petersen
#eval Petersen.numberOfConnectedComponents

-- Search for graphs in the database
#search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }

end LeanHoG
