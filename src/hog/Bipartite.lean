import Mathlib.Algebra.Parity

import Graph
import Walk

namespace Bipartite

open TreeSet
open TreeMap


-- A bipartite graph is a graph together with:
-- · a subset of edges
-- · a function from vertices to {0, 1} s.t.
-- · the subset of edges covers all the vertices of the graph,
-- · the colors of the two endpoints of each of the vertices of the edges in the partition are different
-- structure BipartiteGraph : Type :=
--   (G : SimpleIrreflexiveGraph)
--   (partition : Tset Edge)
--   (cond1 : partition ⊂ G.edges)
--   (full : Tmap (Fin G.vertexSize) Edge)
--   (cond2 : Smap.forall (fun ⟨ _, e ⟩ => Tset.exists (fun e' => e = e') partition) full)
--   (c : Nat → Fin 2)
--   (cond3 : Tset.forall (fun e => c e.edge.fst ≠ c e.edge.snd) partition)

structure VertexLabeling (Label : Type) [DecidableEq Label] (g : SimpleIrreflexiveGraph) : Type where
  label : Nat → Label
  labelCorrect :  ∀ e, e ∈ g.edges → label e.edge.fst ≠ label e.edge.snd

def IsBipartite (G : SimpleIrreflexiveGraph) := ∃ _ : VertexLabeling Bool G, ⊤

lemma EvenOddWalkEndpointEquality
  {G : SimpleIrreflexiveGraph}
  {a b : ℕ}
  (w : Walk G a b)
  (p : VertexLabeling Bool G) :
  (Odd w.length → p.label a ≠ p.label b) ∧
  (Even w.length → p.label a = p.label b)
  := by
  induction w with
  | trivial s isV =>
    apply And.intro
    · intro H
      cases H with
      | intro k eq =>
        simp [Walk.length, Even, Odd] at eq
        contradiction
    · intro
      rfl
  | @left a b c ab w' ih =>
    apply And.intro
    · intro H
      cases H with
      | intro k eq =>
        simp [Walk.length, Even, Odd] at eq
        have wEv : Even w'.length := by simp [eq]
        rw [← ih.right wEv]
        sorry
    · intro H
      sorry
  | right w p =>
    sorry

theorem OddClosedWalkNotBipiartite
  {G : SimpleIrreflexiveGraph}
  (w : ClosedWalk G) :
  Odd w.length → ¬ IsBipartite G := by
  intros isOdd p
  cases p with
  | intro c _ =>
    let _ := (EvenOddWalkEndpointEquality w.snd c).left isOdd
    contradiction

class Bipartite (G : SimpleIrreflexiveGraph) : Type where
  value : Bool
  correct : value ↔ IsBipartite G

end Bipartite
