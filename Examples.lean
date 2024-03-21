import LeanHoG.LoadGraph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Widgets
import LeanHoG.Tactic.SearchDSL

namespace LeanHoG

-- Loading graphs from JSON files, visualizing them, and checking their properties

-- The discrete graph on two vertices
load_graph Two "examples/two.json"
#eval Two.is_connected
#eval Two.numberOfComponents

-- The path of length 1 (on two vertices)
load_graph Path1 "examples/path1.json"
#check Path1.is_bipartite_if_has_certificate

-- The cycle on 7 vertices
load_graph Cycle7 "examples/cycle7.json"
#visualizeGraph Cycle7
#check Cycle7.is_connected

-- The 5-dimensional hypercube from "cube-5.json"
load_graph Cube5 "examples/cube5.json"
#check Cube5.is_connected
#check Cube5.is_bipartite_if_has_certificate

-- The disjoint union of 3- and 4-cycle
load_graph Cow "examples/cycle3-cycle4.json"
#eval Cow.is_connected
#eval Cow.numberOfComponents

#search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }

end LeanHoG
