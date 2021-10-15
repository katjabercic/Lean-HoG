import .raw_hog
import combinatorics.simple_graph.basic
import tactic

namespace hog

open tactic
open tactic.interactive
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident)

def neighbors1 : neighbor_relation := [(0, [4]), (1, [4]), (2,[3]), (3,[2,4]), (4,[0,1,3])]
def adj1 : adjacency_list := [(0, 4), (1, 4), (2, 3), (3, 2), (3, 4), (4, 0), (4, 1), (4, 3)]


def raw_hog00001 := { raw_hog .
  adjacency := adj1,
  acyclic := some ff,
  bipartite := some ff,
  chromatic_index := some (6),
  chromatic_number := some (5),
  circumference := some (7),
  claw_free := some tt,
  clique_number := some (4),
  connected := some tt,
  diameter := some (2),
  edge_connectivity := some (4),
  eulerian := some tt,
  genus := some (1),
  girth := some (3),
  hamiltonian := some tt,
  independence_number := some (2),
  longest_induced_cycle := some (5),
  longest_induced_path := some (3),
  matching_number := some (3),
  maximum_degree := some (6),
  minimum_degree := some (4),
  minimum_dominating_set := some (1),
  number_of_components := some (1),
  number_of_edges := some (16),
  number_of_triangles := some (15),
  number_of_vertices := some (7),
  planar := some ff,
  radius := some (1),
  regular := some ff,
  vertex_connectivity := some (4)
}

structure hog : Type :=
 (raw : hog.raw_hog)
 (preadjacency : hog.preadjacency)
 (graph : simple_graph ℕ)
--  (number_of_vertices_eq_size : raw.number_of_vertices = some (hog.size raw))

meta def roast (e : parse texpr) : tactic unit :=
do { t ← tactic.i_to_expr ``((%%e).number_of_vertices = some (hog.size %%e)),
     (_, p) ← solve_aux t (tactic.reflexivity),
     r ← i_to_expr_strict ``(hog.mk %%e %%p),
     exact r
   }
   
-- #check list.head hog.db_001
-- def hogs : list (list hog) := list.map (λ (rh : hog.raw_hog), by roast rh) (list.head hog.db_001)

end hog