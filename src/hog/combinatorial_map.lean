import .graph
import .tree_set
import .map_path
--import .graph

--namespace combinatorial_map
open tree_set
open map_path
-- To bo moved to a different file

theorem tset_inclusion_size_eq_to_tset_eq {α : Type} [linear_order α] (A : tset α) (B : tset α) : 
  A.size = B.size → (∀ x, x ∈ A → x ∈ B) → (∀ x, x ∈ B → x ∈ A) := sorry
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

def tmap.keys {α β : Type} [linear_order α] (m : tmap α β) : tset α := sorry
def tmap.keys_cond {α β : Type} [linear_order α] (m : tmap α β) : 
  ∀ x, m.contains_key x ↔ x ∈ (tmap.keys m) := sorry
def tmap.keys_size {α β : Type} [linear_order α] (m : tmap α β) :
  m.size = (tmap.keys m).size := sorry
 
def tmap.forall_items {α β : Type} [linear_order α] (p : α → β → bool) :
  tmap α β → bool := sorry
def tmap.forall_items_is_forall {α β : Type} [linear_order α] {p : α → β → bool} :  
  Π {t : tmap α β},
  tmap.forall_items p t → ∀ x y, t.val_at x = some y → p x y := sorry 
def smap.forall_keys {α β : Type} [linear_order α] (p : α → Prop) [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} (t : smap α β b) , bool := sorry
def smap.forall_keys_is_forall {α β : Type} [linear_order α] {p : α → Prop} [decidable_pred p] :
  ∀ {low high : bounded α} {b : low < high} {t : smap α β b}, 
  smap.forall_keys p t = tt → (∀ k, t.contains_key k → p k)
:= sorry
def graph_rotation_consistent (G : simple_irreflexive_graph) (v : ℕ) (c : cycle) : bool :=
  let ns : option (tset ℕ) := (neighbours G).val_at v in
  (match ns with
  | none := ff
  | some v_neigh := is_cycle_of_set c v_neigh
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

def is_cycle_of_opt (σ : tmap ℕ cycle) (x : ℕ) (t : tset ℕ) : bool :=
(match σ.val_at x with
| none := ff
| some c := is_cycle_of_set c t
end)
structure combinatorial_map (G : simple_irreflexive_graph) : Type :=
  (σ : tmap ℕ cycle)
  --(σ_G_consistent : smap.forall_items (graph_rotation_consistent G) σ = tt)
  (G_σ_consistent : tmap.forall_items (λ k t, is_cycle_of_opt σ k t) (neighbours G) = tt)
  (σ_keys_neighbour_keys : smap.forall_keys (λ k, (neighbours G).contains_key k) σ)
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
-- σ maps edges to edges with the same source
def cycle_contains_key_opt (k : ℕ) : option cycle → bool 
| none := ff
| (some c) := c.next.contains_key k
def in_neighbours_opt (G : simple_irreflexive_graph) (x y : ℕ) : Prop :=
(match (neighbours G).val_at x with 
| none := false
| some (x_neigh) := y ∈ x_neigh
end)
/-
  All edges appear in σ and σ only contains edges
-/
theorem σ_edges_consistent {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ x y, cycle_contains_key_opt y (K.σ.val_at x) ↔ in_neighbours_opt G x y :=
begin
  intros x y,
  split,
  -- ->
    intro y_in_σx,
    cases h : K.σ.val_at x with c,
      rw h at y_in_σx,
      simp [cycle_contains_key_opt] at y_in_σx,
      apply false.elim,
      assumption,
  rw h at y_in_σx,
  simp [cycle_contains_key_opt] at y_in_σx,
  let x_in_σ := key_in_map_iff_evals x c h,
  have σ_keys_neigh_keys := (smap.forall_keys_is_forall K.σ_keys_neighbour_keys) x x_in_σ,
  unfold in_neighbours_opt,
  let x_neigh_val := tmap.val_at_safe x σ_keys_neigh_keys,
  let x_neigh_val_cond : some x_neigh_val = (neighbours G).val_at x := tmap.val_at_safe_cond x σ_keys_neigh_keys,
  rw ←x_neigh_val_cond,
  simp [in_neighbours_opt._match_1],
  have G_σ_cons := 
    (tmap.forall_items_is_forall K.G_σ_consistent) x x_neigh_val (eq.symm x_neigh_val_cond),
  simp at G_σ_cons,
  unfold is_cycle_of_opt at G_σ_cons,
  rw h at G_σ_cons,
  simp [is_cycle_of_opt._match_1] at G_σ_cons,
  unfold is_cycle_of_set at G_σ_cons,
  have h' := (to_bool_iff _).mp G_σ_cons,
  cases h' with size_cond h',
  have h' := (to_bool_iff _).mpr h',
  simp at h',
  have h' := stree.forall_is_forall (λ (v : ℕ), ↥(tmap.contains_key v c.next)) x_neigh_val h',  
  simp at h',
  let c_keys := tmap.keys c.next, 
  let c_keys_size := tmap.keys_size c.next,
  let c_keys_cond := tmap.keys_cond c.next,
  have size_cond' : c_keys.size = x_neigh_val.size,
    rw ←c_keys_size,
    assumption,
  have h1 := λ x is_elem, (c_keys_cond x).mp (h' x is_elem),
  have h2 := tset_inclusion_size_eq_to_tset_eq x_neigh_val c_keys (eq.symm size_cond') h1,
  apply h2 y,
  apply (c_keys_cond y).mp,
  assumption,
  -- <-
  intro y_in_neigh_x,
  unfold in_neighbours_opt at y_in_neigh_x,
  cases h : K.σ.val_at x with c, 
    have y_cond := (smap.forall_keys_is_forall K.σ_keys_neighbour_keys) y, 
    simp at y_cond,
    cases h' : (neighbours G).val_at x with x_neigh,
      rw h' at y_in_neigh_x,
      simp [in_neighbours_opt._match_1] at y_in_neigh_x,
      apply false.elim,
      assumption,
    have G_σ_cons := (tmap.forall_items_is_forall K.G_σ_consistent) x x_neigh h',
    simp at G_σ_cons,
    unfold is_cycle_of_opt at G_σ_cons,
    rw h at G_σ_cons,
    simp [is_cycle_of_opt._match_1] at G_σ_cons,
    apply false.elim,
    assumption,
  simp [cycle_contains_key_opt],
  cases h' : (neighbours G).val_at x with x_neigh,
    rw h' at y_in_neigh_x,
    simp [in_neighbours_opt._match_1] at y_in_neigh_x,
    apply false.elim,
    assumption,
  rw h' at y_in_neigh_x,
  simp [in_neighbours_opt._match_1] at y_in_neigh_x,
  have G_σ_cons := (tmap.forall_items_is_forall K.G_σ_consistent) x x_neigh h',
  simp at G_σ_cons,
  unfold is_cycle_of_opt at G_σ_cons,
  rw h at G_σ_cons,
  simp [is_cycle_of_opt._match_1, is_cycle_of_set] at G_σ_cons,
  cases G_σ_cons with size_cond forall_neigh,
  have forall_neigh' := 
    stree.forall_is_forall (λ (v : ℕ), ↥(tmap.contains_key v c.next)) x_neigh forall_neigh,
  apply forall_neigh',
  exact y_in_neigh_x,
end
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
