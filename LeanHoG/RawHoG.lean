
import Lean
import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.Basic
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.HamiltonianPath.Basic


namespace LeanHoG
/--
  JSON representation of invariant values from the House of Graphs.
-/
structure RawHoGData : Type where
  acyclic? : Option Bool
  bipartite? : Option Bool
  chromaticIndex? : Option Nat
  chromaticNumber? : Option Nat
  circumference? : Option Nat
  clawFree? : Option Bool
  cliqueNumber? : Option Nat
  connected? : Option Bool
  degeneracy? : Option Nat
  diameter? : Option Nat
  dominationNumber? : Option Nat
  edgeConnectivity? : Option Nat
  eulerian? : Option Bool
  feedbackVertexSetNumber? : Option Nat
  genus? : Option Nat
  girth? : Option Nat
  groupSize? : Option Nat
  hamiltonian? : Option Bool
  hypohamiltonian? : Option Bool
  hypotraceable? : Option Bool
  independenceNumber? : Option Nat
  lengthOfLongestInducedCycle? : Option Nat
  lengthOfLongestInducedPath? : Option Nat
  lengthOfLongestPath? : Option Nat
  matchingNumber? : Option Nat
  maximumDegree? : Option Nat
  minimumDegree? : Option Nat
  numberOfComponents? : Option Nat
  numberOfEdges? : Option Nat
  numberOfSpanningTrees? : Option Nat
  numberOfTriangles? : Option Nat
  numberOfVertexOrbits? : Option Nat
  numberOfVertices? : Option Nat
  numberOfZeroEigenvalues? : Option Nat
  planar? : Option Bool
  radius? : Option Nat
  regular? : Option Bool
  traceable? : Option Bool
  treewidth? : Option Nat
  twinFree? : Option Bool
  vertexConnectivity? : Option Nat
  vertexCoverNumber? : Option Nat
deriving Lean.FromJson, Lean.ToExpr


class RawHoG (G : Graph) extends RawHoGData

-- The checks returning Bool are commented out in case we need them for a different type of validation

-- check that the number of vertices in the graph matches the value in the database
-- def Graph.checkHoGNumberOfVertices (G : Graph) [R : RawHoG G] : Bool :=
--   decide (R.numberOfVertices? = G.vertexSize)

--  check that the number of edges in the graph matches the value in the database
-- def Graph.checkHoGnumberOfEdges (G : Graph) [R : RawHoG G] : Bool :=
--   R.numberOfEdges? = G.edgeSize

-- check whether the graph is bipartite matches the value in the database
-- def Graph.checkHoGbipartite (G : Graph) [R : RawHoG G] : Bool :=
--   R.bipartite? = decide G.bipartite

-- check that the number of components in the graph matches the value in the database
-- def Graph.checkHoGconnectedComponents (G : Graph) [R : RawHoG G] [C : ConnectedComponents G] : Bool :=
--   R.numberOfComponents? = C.val

-- check whether the graph is connected matches the value in the database
-- def Graph.checkHoGconnected (G : Graph) [R : RawHoG G] [C : ConnectedComponents G] : Bool :=
--   R.connected? = decide (C.val = 1)

-- check whether the graph is traceable matches the value in the database
-- def Graph.checkHoGtraceable (G : Graph) [R : RawHoG G] [HamiltonianPath G] : Bool :=
--   R.traceable? = decide (G.traceable)

end LeanHoG
