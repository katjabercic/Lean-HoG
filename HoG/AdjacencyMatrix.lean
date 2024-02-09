import HoG.Graph

import Mathlib.Data.Matrix.Basic

namespace HoG


/-- The adjacency matrix representing the graph `g`. -/
def Graph.adjacencyMatrix (g : Graph) : Matrix g.vertex g.vertex Bool :=
  Matrix.of g.badjacent


end HoG
