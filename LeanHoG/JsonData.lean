import Lean
-- import LeanHoG.Graph
-- import LeanHoG.Walk
-- import LeanHoG.Invariant.Hamiltonicity.Basic

import LeanHoG.Invariant.Bipartiteness.JsonData
import LeanHoG.Invariant.ConnectedComponents.JsonData
import LeanHoG.Invariant.NeighborhoodMap.JsonData

namespace LeanHoG

/--
  JSON representation of a graph.
-/
structure GraphData : Type where
  vertexSize : Nat
  edges : Array (Nat × Nat)
deriving Lean.FromJson

/-- JSON representation of a path in a graph -/
structure PathData : Type where
  vertices : List Nat
deriving Lean.FromJson

/--
  JSON representation of a graph together with invariants.
-/
structure JSONData : Type where
  hogId : Option Nat
  graph : GraphData

  /- Invariants are optional -/
  connectedComponents? : Option ConnectedComponentsData
  pathData? : Option PathData
  bipartiteness? : Option BipartitenessData
  neighborhoodMap? : Option NeighborhoodMapData

deriving Lean.FromJson

/-- Load the JSon representation of a graph with invariants from a file. -/
def loadJSONData (filePath : System.FilePath) : IO JSONData := do
  let fileContent ← IO.FS.readFile filePath
  match Lean.Json.parse fileContent >>= Lean.FromJson.fromJson? (α := JSONData) with
  | .ok data => pure data
  | .error msg => throw (.userError msg)

end LeanHoG
