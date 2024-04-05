import LeanHoG.Graph
import LeanHoG.Widgets
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanSAT

import Std.Data.RBMap.Basic

namespace LeanHoG

open LeanSAT

def no_ham : Graph :=
  {
    vertexSize := 3,
    edgeTree := Std.RBSet.ofList [(Edge.mk 1 ⟨2, by norm_num⟩ (by norm_num)), (Edge.mk 0 ⟨1, by norm_num⟩ (by norm_num))] Edge.linearOrder.compare
  }

instance : Solver IO := Solver.Impl.DimacsCommand "kissat"

#eval showNoHamiltonianPath no_ham

#visualizeHamiltonianPath? no_ham


























abbrev g1 : Graph :=
  {
    vertexSize := 2,
    edgeTree := Std.RBSet.ofList [Edge.mk 0 ⟨1, by norm_num⟩ (by norm_num)] Edge.linearOrder.compare
  }

#widget visualize with g1.toVisualizationFormat

def w : Walk g1 0 1 :=
  .left (by decide) (.trivial 1)

def p : Path g1 0 1 := {
  walk := w
}
instance : HamiltonianPath g1 where
  u := 0
  v := 1
  path := p

#visualizeHamiltonianPath g1



end LeanHoG
