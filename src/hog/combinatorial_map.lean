import .graph
import .tree_set
import .map_path
--import .graph

--namespace combinatorial_map
open tree_set
open map_path
-- To bo moved to a different file

-- Apply the tmap next n times to some starting parameter

-- create an edge from two natural numbers
def create_edge (u v : ℕ) (q : u ≠ v) : Edge :=
  decidable.lt_by_cases u v
  (λ _, {Edge. edge := (u, v)})
  (λ _, {Edge. edge := (u, v)})
  (λ _, {Edge. edge := (v, u)})

/-
  end of things to be moved
-/

def walk_with (start : ℕ) (next : tmap ℕ ℕ) : list ℕ → ℕ → bool
| [] n := (
  match next.val_at n with
  | none := ff
  | some val := val = start
  end
)
| (x :: xs) n := x = n ∧ 
  (match next.val_at n with 
  | none := ff
  | some val := walk_with xs val
  end : bool)

def is_cycle_b (next : tmap ℕ ℕ) : bool :=
(match next with -- to start the walk we need to get some initial key
| (smap.empty _) := tt
| (smap.leaf k v _ _) := walk k next v (next.size - 1)
| (smap.node k v _ _) :=  walk k next v (next.size - 1)
end)

-- for any two elements we can use next some finite number of times to get from the first to the second
def cycle_prop (next : tmap ℕ ℕ) := ∀ (x y : ℕ), next.contains_key x → next.contains_key y → 
  ∃ (n : ℕ), tmap_iter next x n = some y

structure cycle : Type :=
  (next : tmap ℕ ℕ)
  (is_cycle : is_cycle_b next = tt)



def is_cycle_of_set (c : cycle) (t : tset ℕ) : bool :=
  (smap.size (c.next) = t.size) ∧
  (t.forall (λ v, c.next.contains_key v))

-- checks that α ∘ σ (x, y) = (y, z)
def σα_maps (σ : tmap ℕ cycle) (x y z : ℕ) : bool :=
(match σ.val_at y with
| none := ff
| some c := (
  match c.next.val_at x with
  | none := ff
  | some val := z = val
  end
  )
end)

def is_list_of_σα_aux (σ : tmap ℕ cycle) (fst : ℕ) (snd : ℕ) : list ℕ → bool
| [] := tt
| (x :: []) := σα_maps σ x fst snd
| (x :: y :: []) := σα_maps σ x y fst
| (x :: l@(y :: z :: xs)) := σα_maps σ x y z ∧ is_list_of_σα_aux l

-- check that list is a cycle for σα
def is_list_of_σα (σ : tmap ℕ cycle) : list ℕ → bool
| [] := ff -- empty lists shouldn't be present
| (x :: []) := (
  match σ.val_at x with
  | none := ff -- element isn't even in the map
  | some c := c.next.size = 0 -- list has one element only if vertex is isolated
  end
  )
| l@(x :: y :: xs) := is_list_of_σα_aux σ x y l

def neighbours (G : simple_irreflexive_graph) : tmap ℕ (tset ℕ) := sorry
 
def smap.forall_items (p : (ℕ → (cycle) → bool)) :
  ∀ {low high : bounded ℕ} {b : low < high} (t : smap ℕ (cycle) b) , bool := sorry

def graph_rotation_consistent (G : simple_irreflexive_graph) (v : ℕ) (c : cycle) : bool :=
  let ns : option (tset ℕ) := (neighbours G).val_at v in
  (match ns with
  | none := ff
  | some val := is_cycle_of_set c val
  end : bool)

-- constructs an edge and adds it to a tset Edge
def add_edge_aux (x y : ℕ) (es : tset Edge) : tset Edge :=
(decidable.lt_by_cases x y
    (λ _, let e := {Edge. edge := (x, y)} in es.add e)
    (λ _, es)
    (λ _, let e := {Edge. edge := (y, x)} in es.add e)
    )

-- takes all pairs of consecuative numbers to generate edges and add them to a tset 
def add_edges_from_face_aux : ℕ → tset Edge → list ℕ → tset Edge
| start es [] := es
| start es (x :: []) := add_edge_aux x start es
| start es (x :: y :: xs) := add_edges_from_face_aux start (add_edge_aux x y es) xs
--def face_map (σ : tmap ℕ cycle) : tmap ℕ cycle 

-- Given a list of faces (represented as lists) add all edges to a tset Edge
def add_edges_from_face_list : (list (list ℕ)) → tset Edge → tset Edge 
| [] edges := edges
| ([] :: fs) edges := add_edges_from_face_list fs edges
| (f@(x :: xs) :: fs) edges := add_edges_from_face_list fs (add_edges_from_face_aux x edges f)

structure combinatorial_map (G : simple_irreflexive_graph) : Type :=
  (σ : tmap ℕ cycle)
  (σ_G_consistent : smap.forall_items (graph_rotation_consistent G) σ = tt)
  (faces : list (list ℕ))
  (composition_faces_consistent : faces.all (is_list_of_σα σ)) -- shows that every face is in fact the face of σ ∘ α
  --shows that every face is present by checking that the correct number of edges is present
  (num_of_edges : 
    let empty_set : tset Edge := stree.empty (by trivial) in
    -- here add doesn't work as intended
    let combined_edges : tset Edge := 
      add_edges_from_face_list faces empty_set in
    combined_edges.size = 2 * G.edge_size
  )
  
  -- might still require checking if list actually contains edges

-- Given the cycle structure we in fact have a cycle
theorem cycle_is_cycle_prop (c : cycle) : cycle_prop (c.next) :=
begin
  cases c with next is_cycle,
  unfold cycle_prop,
  unfold is_cycle_b at is_cycle,
  intros x y x_in_map y_in_map,
  cases next,
    -- The empty map case
    simp [tmap.contains_key] at x_in_map,
    apply false.elim x_in_map,
  -- The leaf case
  split,
    show ℕ, from 0,
  simp [tmap_iter],
  simp [tmap.contains_key] at x_in_map y_in_map,
  rw y_in_map,
  assumption,
  -- The node case
  simp [is_cycle_b._match_1] at is_cycle,
  have elem_cond := 
    path_of_length_size_all_keys 
      (walk_to_path is_cycle) 
      (walk_to_path_end_unique is_cycle)
      (by simp [tmap.contains_key, smap.contains_key, decidable.lt_by_cases])
      begin
        rw walk_to_path_size is_cycle,
        have h : 1 ≤ (smap.node next_key next_val next_left next_right).size, 
          simp [smap.size],
          rw add_assoc,
          rw add_comm,
          simp,
        rw nat.sub_add_cancel h,
      end,
  have x_in_path := elem_cond x x_in_map,
  have y_in_path := elem_cond y y_in_map,
  have x_to_dst := elem_to_dst (walk_to_path is_cycle) x_in_path,
  have src_to_y := src_to_elem (walk_to_path is_cycle) y_in_path,
  have next_key_to_next_val : map_next_is (smap.node next_key next_val next_left next_right) next_key next_val,
    simp [map_next_is, tmap.val_at, smap.val_at, decidable.lt_by_cases],
  have x_to_y := map_path_append x_to_dst src_to_y next_key_to_next_val,
  split,
    show ℕ, from x_to_y.size,
  exact map_path_iter_src_dst x_to_y,
end
