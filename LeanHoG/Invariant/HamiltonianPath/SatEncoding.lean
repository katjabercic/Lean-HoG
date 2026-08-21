import LeanHoG.Graph
import LeanHoG.Invariant.HamiltonianPath.Basic
import LeanHoG.Sat.Grid

import Trestle.Model.PropFun
import Trestle.Encode.VEncCNF
import Trestle.Solver.Basic
import LeanHoG.Util.TrestleStd

namespace LeanHoG

open Lean Trestle Encode VEncCNF Meta Model PropFun
open Sat

/-! This encoding is the *square* grid: `Grid.Var G.vertexSize G.vertexSize`, where
`Grid.Var.mk i j` means "at position `j` on the path is vertex `i`". A Hamiltonian path visits
each of the `n` vertices exactly once, so it has exactly as many positions as vertices — and that
is the whole of what distinguishes it from the cycle encoding, which is `n × (n + 1)` because its
last position repeats its first.

Both dimensions are written out at every use below rather than hidden behind an abbreviation,
because the pair of them *is* the difference between the two encodings. -/

/-- Each vertex is at some position, and no vertex is at two positions.

Unlike the cycle, the path exempts no position, so this is `Grid.rowAmo` rather than
`Grid.rowAmoOn`. -/
@[simp] def vertexConstraints (G : Graph) : PropPred (Grid.Var G.vertexSize G.vertexSize) := fun τ =>
  (τ |> Grid.rowNonempty G.vertexSize G.vertexSize) ∧
  (τ |> Grid.rowAmo G.vertexSize G.vertexSize)

/-- Each position holds some vertex, and no position holds two vertices. -/
@[simp] def positionConstraints (G : Graph) : PropPred (Grid.Var G.vertexSize G.vertexSize) := fun τ =>
  (τ |> Grid.colNonempty G.vertexSize G.vertexSize) ∧
  (τ |> Grid.colAmo G.vertexSize G.vertexSize)

/-- Vertices at consecutive positions on the path are adjacent in `G`. -/
@[simp] def edgeConstraints (G : Graph) : PropPred (Grid.Var G.vertexSize G.vertexSize) := fun τ =>
  (τ |> Grid.consecutiveRelated G.vertexSize G.vertexSize G.adjacent)

@[simp] def hamiltonianPathConstraints (G : Graph) : PropPred (Grid.Var G.vertexSize G.vertexSize) := fun τ =>
  (τ |> vertexConstraints G) ∧ (τ |> positionConstraints G) ∧ (τ |> edgeConstraints G)

----------------------------------------------------------------------------------------
-- Express the problem as a CNF

open Encode VEncCNF LitVar

/-! Each builder below is an assembly of `LeanHoG/Sat/Grid.lean` atoms and says nothing about how
a clause is emitted. The choice of atoms and the `seq` order are what fix the emitted DIMACS, so
they match the hand-written encoding they replace arm for arm; the `mapProp`s only restate the
resulting `Prop` as the bundle above, which provably cannot change a byte. -/

def vertexClauses (G : Graph) : Grid.VCnf G.vertexSize G.vertexSize (vertexConstraints G) :=
  (seq[
    Grid.rowNonemptyClauses G.vertexSize G.vertexSize,
    Grid.rowAmoClauses G.vertexSize G.vertexSize
  ])
  |> mapProp (by
    ext τ
    simp
  )

def positionClauses (G : Graph) : Grid.VCnf G.vertexSize G.vertexSize (positionConstraints G) :=
  (seq[
    Grid.colNonemptyClauses G.vertexSize G.vertexSize,
    Grid.colAmoClauses G.vertexSize G.vertexSize
  ])
  |> mapProp (by
    ext τ
    simp
  )

def edgeClauses (G : Graph) : Grid.VCnf G.vertexSize G.vertexSize (edgeConstraints G) :=
  (Grid.consecutiveRelatedClauses G.vertexSize G.vertexSize G.adjacent)
  |> mapProp (by
    ext τ
    simp
  )

def hamiltonianPathCNF (G : Graph) : Grid.VCnf G.vertexSize G.vertexSize (hamiltonianPathConstraints G) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G
  ])
  |> mapProp (by aesop)

end LeanHoG
