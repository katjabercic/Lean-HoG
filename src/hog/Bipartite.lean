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

class Bipartite (g : SimpleIrreflexiveGraph) : Type where
  partition : Nat → Fin 2
  cond : Stree.forall (fun e => partition e.edge.fst ≠ partition e.edge.snd) g.edges

class NonBipartite (g : SimpleIrreflexiveGraph) : Type where
  u : Nat
  closedWalk : ClosedWalk g u
  isOdd : Odd (closedWalk.length)

end Bipartite