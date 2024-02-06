import Lean
import JSON2Lean.MapTree
import JSON2Lean.Graph

namespace JSON2Lean

/--
  A structure that corresponds to the JSON description of a graph.
-/
structure GraphData : Type where
  vertexSize : Nat
  edges : Array (Nat × Nat)
deriving Lean.FromJson

/--
  A structure that corresponds to the JSON description of connectivity certificate.
-/
structure ConnectivityData : Type where
  /-- The root of the spanning tree. -/
  root : Nat

  /--
  For each vertex that is not a root, the next step of the path leading to the
  root (and the root maps to itself).
  -/
  next : Array (Nat × Nat)

  /--
  To ensure that next is cycle-free, we witness the fact that "next" takes us closer to the root.
  the distance of a vertex to its component root
  -/
  distToRoot : Array (Nat × Nat)

deriving Lean.FromJson


/--
  A structure that corresponds to the JSON description of disconnectivity certificate.
-/
structure DisconnectivityData : Type where

  /-- A coloring of vertices by two colors -/
  color : Array (Nat × Nat)

  /-- A vertex of color 0 -/
  vertex0 : Nat

  /-- A vertex of color 1-/
  vertex1 : Nat
deriving Lean.FromJson

/--
  A structure that corresponds to the JSON description of a graph and optional
  connectivity and disconnectivity certificates.
-/
structure GAPData : Type where
  graph : GraphData
  connectivityData? : Option ConnectivityData
  disconnectivityData? : Option DisconnectivityData
deriving Lean.FromJson

def loadGAPData (filePath : System.FilePath) : IO GAPData := do
  let fileContent ← IO.FS.readFile filePath
  match Lean.Json.parse fileContent >>= Lean.FromJson.fromJson? (α := GAPData) with
  | .ok data => pure data
  | .error msg => throw (.userError msg)

end JSON2Lean
