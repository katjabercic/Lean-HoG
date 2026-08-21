import LeanHoG.Graph
import LeanHoG.Invariant.HamiltonianCycle.Basic
import LeanHoG.Sat.Grid

import Trestle.Model.PropFun
import Trestle.Encode.VEncCNF
import Trestle.Solver.Basic
import LeanHoG.Util.TrestleStd

namespace LeanHoG

/- Still namespaced, though the encoding it used to hold is now shared. `LeanHoG/Sat/Grid.lean`
    owns the variables and the clauses; what is left here is the per-property assembly, and its
    five bundle names (`vertexConstraints`, `positionConstraints`, `edgeConstraints`, ...) are
    the same on both sides, because both `Correctness.lean` files address them by those names.
    So the two files still collide, and this keeps them apart. -/
namespace HamiltonianCycle

open Lean Trestle Encode VEncCNF Meta Model PropFun
open Sat

/-! This encoding is the `n × (n + 1)` grid: `Grid.Var G.vertexSize (G.vertexSize + 1)`, where
`Grid.Var.mk i j` means "at position `j` on the cycle is vertex `i`". A cycle on `n` vertices has
`n + 1` positions, because it closes up by repeating its first vertex at the last one.

That extra column is the source of both remaining differences from the path encoding, which is the
square grid. A vertex may occupy two positions when they are the first and the last, so the
at-most-one-position constraint exempts column `0` — `Grid.rowAmoOn` rather than `Grid.rowAmo`. And
since a Hamiltonian cycle passes through every vertex anyway, vertex `0` can be pinned into both of
those positions without loss of generality, which shrinks the search space.

Both dimensions are written out at every use below rather than hidden behind an abbreviation,
because the pair of them *is* the difference between the two encodings. -/

/-- Each vertex is at some position, and no vertex is at two positions — except the endpoints,
which are the same position on the cycle and so hold the same vertex. -/
@[simp] def vertexConstraints (G : Graph) :
    PropPred (Grid.Var G.vertexSize (G.vertexSize + 1)) := fun τ =>
  (τ |> Grid.rowNonempty G.vertexSize (G.vertexSize + 1)) ∧
  (τ |> Grid.rowAmoOn G.vertexSize (G.vertexSize + 1) (fun j => 0 < j.val))

/-- Each position holds some vertex, and no position holds two vertices. -/
@[simp] def positionConstraints (G : Graph) :
    PropPred (Grid.Var G.vertexSize (G.vertexSize + 1)) := fun τ =>
  (τ |> Grid.colNonempty G.vertexSize (G.vertexSize + 1)) ∧
  (τ |> Grid.colAmo G.vertexSize (G.vertexSize + 1))

/-- Vertices at consecutive positions on the cycle are adjacent in `G`. -/
@[simp] def edgeConstraints (G : Graph) :
    PropPred (Grid.Var G.vertexSize (G.vertexSize + 1)) := fun τ =>
  (τ |> Grid.consecutiveRelated G.vertexSize (G.vertexSize + 1) G.adjacent)

/-- WLOG the cycle starts and ends at vertex `0`. `h` is needed only to name that vertex; the
grid atoms take the index already built, which is what keeps `Grid.lean` free of `Fin` literals
and of any `NeZero` hypothesis. -/
@[simp] def firstAndLastConstraints (G : Graph) (h : 0 < G.vertexSize) :
    PropPred (Grid.Var G.vertexSize (G.vertexSize + 1)) := fun τ =>
  (τ |> Grid.pin G.vertexSize (G.vertexSize + 1) ⟨0, h⟩ 0) ∧
  (τ |> Grid.pin G.vertexSize (G.vertexSize + 1) ⟨0, h⟩ ⟨G.vertexSize, lt_add_one G.vertexSize⟩)

/-- A graph has a Hamiltonian cycle if it satisfies all of the above constraints. -/
@[simp] def hamiltonianCycleConstraints (G : Graph) (h : 0 < G.vertexSize) :
    PropPred (Grid.Var G.vertexSize (G.vertexSize + 1)) := fun τ =>
  (τ |> vertexConstraints G) ∧ (τ |> positionConstraints G) ∧
  (τ |> edgeConstraints G) ∧ (τ |> firstAndLastConstraints G h)

----------------------------------------------------------------------------------------
-- Express the problem as a CNF

open Encode VEncCNF LitVar

/-! Each builder below is an assembly of `LeanHoG/Sat/Grid.lean` atoms and says nothing about how
a clause is emitted. The choice of atoms and the `seq` order are what fix the emitted DIMACS, so
they match the hand-written encoding they replace arm for arm; the `mapProp`s only restate the
resulting `Prop` as the bundle above, which provably cannot change a byte. -/

def vertexClauses (G : Graph) :
    Grid.VCnf G.vertexSize (G.vertexSize + 1) (vertexConstraints G) :=
  (seq[
    Grid.rowNonemptyClauses G.vertexSize (G.vertexSize + 1),
    Grid.rowAmoOnClauses G.vertexSize (G.vertexSize + 1) (fun j => 0 < j.val)
  ])
  |> mapProp (by
    ext τ
    simp
  )

def positionClauses (G : Graph) :
    Grid.VCnf G.vertexSize (G.vertexSize + 1) (positionConstraints G) :=
  (seq[
    Grid.colNonemptyClauses G.vertexSize (G.vertexSize + 1),
    Grid.colAmoClauses G.vertexSize (G.vertexSize + 1)
  ])
  |> mapProp (by
    ext τ
    simp
  )

def edgeClauses (G : Graph) :
    Grid.VCnf G.vertexSize (G.vertexSize + 1) (edgeConstraints G) :=
  (Grid.consecutiveRelatedClauses G.vertexSize (G.vertexSize + 1) G.adjacent)
  |> mapProp (by
    ext τ
    simp
  )

def firstAndLastVertexClauses (G : Graph) (h : 0 < G.vertexSize) :
    Grid.VCnf G.vertexSize (G.vertexSize + 1) (firstAndLastConstraints G h) :=
  (seq[
    Grid.pinClauses G.vertexSize (G.vertexSize + 1) ⟨0, h⟩ 0,
    Grid.pinClauses G.vertexSize (G.vertexSize + 1) ⟨0, h⟩ ⟨G.vertexSize, lt_add_one G.vertexSize⟩
  ])
  |> mapProp (by
    ext τ
    simp
  )

def hamiltonianCycleCNF (G : Graph) (h : 0 < G.vertexSize) :
    Grid.VCnf G.vertexSize (G.vertexSize + 1) (hamiltonianCycleConstraints G h) :=
  (seq[
    vertexClauses G, positionClauses G, edgeClauses G, firstAndLastVertexClauses G h
  ])
  |> mapProp (by aesop)

end HamiltonianCycle
end LeanHoG
