import combinatorics.simple_graph.basic
import .decode

-- The definition of data imported from HoG
structure hog : Type :=
 (chromatic_number : ℕ)
 (genus : ℕ)
 (girth : ℕ)
 (graph6 : string)
 (is_eulerian : bool)
 (is_hamiltonian : bool)
 (maximum_degree : ℕ)
 (minimum_degree : ℕ)
 (number_of_vertices : ℕ)

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
