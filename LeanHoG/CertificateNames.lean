import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.RawHoG

namespace LeanHoG

open Lean

/-- A Lean name for a certificate -/
def concatenateName (graphName: Name) (certName: String) : Name :=
  (.str graphName certName)

/-- A Lean name for a the HoG values structure -/
def RawHoG.name (graphName: Name) : Name :=
  concatenateName graphName "RawHoG"

/-- A Lean name for the connected components certificate -/
def ConnectedComponentsCertificate.name (graphName: Name) : Name :=
  concatenateName graphName "ConnectedComponentsCertificateI"

/-- A Lean name for the two-coloring certificate -/
def TwoColoring.name (graphName: Name) : Name :=
  concatenateName graphName "TwoColoringI"

/-- A Lean name for the odd closed walk certificate -/
def OddClosedWalk.name (graphName: Name) : Name :=
  concatenateName graphName "OddClosedWalkI"

/-- A Lean name for the neighbourhood map -/
def NeighborhoodMap.name (graphName: Name) : Name :=
  concatenateName graphName "NeighborhoodMapI"

end LeanHoG
