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

structure VertexPartition (Label : Type) [DecidableEq Label] (g : SimpleIrreflexiveGraph) : Type where
  partition : Nat → Label
  partitionCorrect : Stree.forall (fun e => partition e.edge.fst ≠ partition e.edge.snd) g.edges

def IsBipartite (G : SimpleIrreflexiveGraph) := ∃ _ : VertexPartition Bool G, ⊤

inductive BipartiteCertificate (G : SimpleIrreflexiveGraph): Type where
  | partition : VertexPartition Bool G → BipartiteCertificate G
  | oddClosedWalk (w : ClosedWalk G) : Odd (w.length) → BipartiteCertificate G

def certToBool {G : SimpleIrreflexiveGraph} : BipartiteCertificate G → Bool
  | .partition _ => true
  | .oddClosedWalk _ _ => false

theorem certCorrect {G : SimpleIrreflexiveGraph} (C : BipartiteCertificate G):
  IsBipartite G ↔ certToBool C = true := by
  sorry

class Bipartite (G : SimpleIrreflexiveGraph) : Type where
  asBool : Bool
  cert : BipartiteCertificate G
  asBoolCorrect : asBool ↔ IsBipartite G

end Bipartite