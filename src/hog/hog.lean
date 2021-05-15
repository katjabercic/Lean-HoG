import combinatorics.simple_graph.basic
import data.real.basic
import .decode

-- The definition of data imported from HoG
structure hog : Type :=
 (graph6 : string)
 (acyclic : option bool)
 (algebraic_connectivity : option real)
 (average_degree : option real)
 (bipartite : option bool)
 (chromatic_index : option nat)
 (chromatic_number : option nat)
 (circumference : option nat)
 (claw_free : option bool)
 (clique_number : option nat)
 (connected : option bool)
 (density : option real)
 (diameter : option nat)
 (edge_connectivity : option nat)
 (eulerian : option bool)
 (genus : option nat)
 (girth : option nat)
 (hamiltonian : option bool)
 (independence_number : option nat)
 (index : option real)
 (laplacian_largest_eigenvalue : option real)
 (longest_induced_cycle : option nat)
 (longest_induced_path : option nat)
 (matching_number : option nat)
 (maximum_degree : option nat)
 (minimum_degree : option nat)
 (minimum_dominating_set : option nat)
 (number_of_components : option nat)
 (number_of_edges : option nat)
 (number_of_triangles : option nat)
 (number_of_vertices : option nat)
 (planar : option bool)
 (radius : option nat)
 (regular : option bool)
 (second_largest_eigenvalue : option real)
 (smallest_eigenvalue : option real)
 (vertex_connectivity : option nat)

namespace hog

-- the size of the graph as encoded by graph6
def graph6_size (h : hog) : ℕ :=
  (decode_graph6 (graph6 h)).fst

-- raw lookup into adjacency matrix
def graph6_lookup (h : hog) : (fin (graph6_size h)) → (fin (graph6_size h)) → Prop :=
  λ i j, (decode_graph6 (graph6 h)).snd i.val j.val

def to_simple_graph (h : hog) : simple_graph (fin (graph6_size h)) :=
    simple_graph.from_rel (graph6_lookup h)

end hog
