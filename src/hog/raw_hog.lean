import .decode

namespace hog

def neighbor_relation : Type := list (ℕ × list ℕ)
def adjacency_list: Type := list (ℕ × ℕ)
def preadjacency := ℕ → ℕ → bool

#check neighbor_relation

-- The definition of data imported from HoG
structure raw_hog : Type :=
 (neighborhoods : neighbor_relation)
 (adjacency: adjacency_list)
 (acyclic : option bool)
 (bipartite : option bool)
 (chromatic_index : option nat)
 (chromatic_number : option nat)
 (circumference : option nat)
 (claw_free : option bool)
 (clique_number : option nat)
 (connected : option bool)
 (diameter : option nat)
 (edge_connectivity : option nat)
 (eulerian : option bool)
 (genus : option nat)
 (girth : option nat)
 (hamiltonian : option bool)
 (independence_number : option nat)
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
 (vertex_connectivity : option nat)

-- def size (h : raw_hog) : ℕ := graph6_size h.graph6

-- instance raw_hog_decidable_adj (h : raw_hog) : decidable_rel (to_simple_graph h).adj :=
--   begin
--     intros i j, 
--     unfold to_simple_graph,
--     simp,
--     unfold graph6_rel,
--     apply_instance,
--   end

end hog
