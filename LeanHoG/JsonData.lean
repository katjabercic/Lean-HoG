import Lean

import LeanHoG.Invariant.Bipartite.JsonData
import LeanHoG.Invariant.ConnectedComponents.JsonData
import LeanHoG.Invariant.NeighborhoodMap.JsonData
import LeanHoG.Invariant.HamiltonianPath.JsonData

namespace LeanHoG

/--
  JSON representation of a graph.
-/
structure GraphData : Type where
  vertexSize : Nat
  edges : Array (Nat × Nat)
deriving Lean.FromJson

/--
  JSON representation of invariant values from the House of Graphs.
-/
structure RawHoG : Type where
  acyclic? : Option Bool
  bipartite? : Option Bool
  chromaticIndex? : Option Nat
  chromaticNumber? : Option Nat
  circumference? : Option Nat
  clawFree? : Option Bool
  cliqueNumber? : Option Nat
  connected? : Option Bool
  degeneracy? : Option Nat
  density? : Option Nat
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
deriving Lean.FromJson

/--
  JSON representation of a graph together with invariants.
-/
structure JSONData : Type where
  hogId : Option Nat
  graph : GraphData
  rawHoG? : Option RawHoG

  /- Invariants are optional -/
  connectedComponents? : Option ConnectedComponentsData
  hamiltonianPath? : Option HamiltonianPathData
  twoColoring? : Option TwoColoringData
  oddClosedWalk? : Option OddClosedWalkData
  neighborhoodMap? : Option NeighborhoodMapData

deriving Lean.FromJson

/-- Load the JSON representation of a graph with invariants from a file. -/
def loadJSONData (α : Type) [Lean.FromJson α] (filePath : System.FilePath) : IO α := do
  let fileContent ← IO.FS.readFile filePath
  match Lean.Json.parse fileContent >>= Lean.FromJson.fromJson? (α := α) with
  | .ok data => pure data
  | .error msg => throw (.userError msg)

end LeanHoG
