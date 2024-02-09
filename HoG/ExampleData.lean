import HoG.Graph
import HoG.Invariant.EdgeSize
import HoG.Invariant.Hamiltonian.SatEncoding
import LeanSAT

namespace HoG

open LeanSAT Model

def piglet1 : Graph :=
  { vertexSize := 3,
    edgeTree := .node (Edge.mk 2 ⟨0, by simp⟩) (.leaf (Edge.mk 1 ⟨0, by simp⟩)) (.leaf (Edge.mk 2 ⟨1, by simp⟩)) }

instance : EdgeSize piglet1 where
  val := 3
  correct := by rfl

instance : Solver IO := Solver.Impl.DimacsCommand "kissat"

#eval (findHamiltonianCycle piglet1)

--======================================
-- Smaller example, path with 2 vertices
--======================================

def piglet0 : Graph :=
  { vertexSize := 2,
    edgeTree := .node (Edge.mk 1 ⟨0, by simp⟩) .empty .empty }

#eval (findHamiltonianCycle piglet0)

def Pos := Fin 2 × Fin 2
deriving ToString

open PropForm.Notation in
def formula : PropForm Pos :=
  let x_00 : PropForm Pos := .var (0,0)
  let x_01 : PropForm Pos := .var (0,1)
  let x_10 : PropForm Pos := .var (1,0)
  let x_11 : PropForm Pos := .var (1,1)
  (x_00 ∨ x_01) ∧ (x_10 ∨ x_11) ∧
  (x_00 ∨ x_10) ∧ (x_01 ∨ x_11) ∧
  (¬x_00 ∨ ¬x_01) ∧ (¬x_01 ∨ ¬x_00) ∧
  (¬x_10 ∨ ¬x_11) ∧ (¬x_11 ∨ ¬x_10) ∧
  (¬x_00 ∨ ¬x_10) ∧ (¬x_10 ∨ ¬x_00) ∧ (¬x_01 ∨ ¬x_11) ∧ (¬x_11 ∨ ¬x_01) ∧
  (¬x_00 ∨ ¬x_10) ∧ (¬x_01 ∨ ¬x_11)

def assignment : PropAssignment Pos
  | (0,0) => true
  | (0,1) => false
  | (1,0) => false
  | (1,1) => true

def prop_fun : PropFun Pos := ⟦formula⟧

theorem encoding_correct : (∃ (u v : piglet0.vertex) (p : Path piglet0 u v), p.isHamiltonian) ↔
  (∃ (τ : PropAssignment Pos), PropFun.satisfies τ prop_fun) := by
  apply Iff.intro
  · -- Idea: Use the Hamiltonian path to construct a satisfying assignment
    intro h
    let ⟨u,v,p,h⟩ := h
    have q : piglet0.vertex = Fin 2 := rfl
    let τ : PropAssignment Pos := fun pos =>
      match pos with
      | (0,0) => (u == (q ▸ 0))
      | (0,1) => (u == (q ▸ 1))
      | (1,0) => (v == (q ▸ 0))
      | (1,1) => (v == (q ▸ 1))
    have : PropFun.satisfies τ prop_fun := by
      sorry
    apply Exists.intro
    exact this
  · -- Idea: Use the satisfying assignment to construct a Hamiltonian path
    -- Take u := xᵢ,₀, v := xⱼ,₁ for the i,j where they are true in τ
    -- Use the properties of the encoding to show this gives you a path.
    intro h
    let ⟨τ,h⟩ := h
    sorry

end HoG
