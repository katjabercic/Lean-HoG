
import Lean
import LeanHoG.Graph


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


/-- check that the number of vertices in the graph matches the value in the database -/
def Graph.checkHoGnumberOfVertices (G : Graph) [R : RawHoG G] : Bool :=
  R.numberOfVertices? = G.vertexSize

/-- check that the number of edges in the graph matches the value in the database -/
def Graph.checkHoGnumberOfEdges (G : Graph) [R : RawHoG G] : Bool :=
  R.numberOfEdges? = G.edgeSize

end LeanHoG
