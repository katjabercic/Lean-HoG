import .decode
import .hog

def hog_graph := { hog .
  graph6 := "FqN~w",
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

class verify_number_of_vertices (g : hog) :=
  (correct_size : hog.number_of_vertices g = some (hog.decode_graph6 (hog.graph6 g)).fst)

instance foo : verify_number_of_vertices hog_graph := {
  correct_size := refl _
}

-- #eval correct_size foo