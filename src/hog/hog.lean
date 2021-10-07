import .raw_hog

namespace hog

structure hog : Type :=
 (raw : raw_hog)
 (number_of_vertices_eq_size : raw.number_of_vertices = some (size raw))
--  (graph6 : string)
--  (acyclic : option bool)
--  (bipartite : option bool)
--  (chromatic_index : option nat)
--  (chromatic_number : option nat)
--  (circumference : option nat)
--  (claw_free : option bool)
--  (clique_number : option nat)
--  (connected : option bool)
--  (diameter : option nat)
--  (edge_connectivity : option nat)
--  (eulerian : option bool)
--  (genus : option nat)
--  (girth : option nat)
--  (hamiltonian : option bool)
--  (independence_number : option nat)
--  (longest_induced_cycle : option nat)
--  (longest_induced_path : option nat)
--  (matching_number : option nat)
--  (maximum_degree : option nat)
--  (minimum_degree : option nat)
--  (minimum_dominating_set : option nat)
--  (number_of_components : option nat)
--  (number_of_edges : option nat)
--  (number_of_triangles : option nat)
--  (number_of_vertices : option nat)
--  (planar : option bool)
--  (radius : option nat)
--  (regular : option bool)
--  (vertex_connectivity : option nat)

-- This does not work
-- instance number_of_vertices_eq_size (h : hog) : h.raw.number_of_vertices = some (size h.raw) :=
-- begin
--   obviously
-- end

end hog