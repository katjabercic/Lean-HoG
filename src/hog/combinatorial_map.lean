import .graph
import .tree_set
--import .graph

--namespace combinatorial_map
open tree_set

-- To bo moved to a different file

-- Apply the tmap next n times to some starting parameter
def tmap_apply {α : Type} [linear_order α] (next : tmap α α) : α → ℕ → option α
| x 0 := x
| x (n + 1) := 
  (match next.val_at x with
  | none := none
  | some a := tmap_apply a n
  end)

-- create an edge from two natural numbers
def create_edge (u v : ℕ) (q : u ≠ v) : Edge :=
  decidable.lt_by_cases u v
  (λ _, {Edge. edge := (u, v)})
  (λ _, {Edge. edge := (u, v)})
  (λ _, {Edge. edge := (v, u)})
--structure cycle {α : Type} [linear_order α] : Type :=
  --(carrier : tset α)
-- def next_in_tree (next : tmap ℕ ℕ) : next.
def walk (start : ℕ) (next : tmap ℕ ℕ) : ℕ → ℕ → bool
| cur 0 := start = cur
| cur (n + 1) := 
  start ≠ cur ∧
  (match next.val_at cur with
  | none := ff
  | some val := walk val n 
  end : bool)

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

def is_cycle (next : tmap ℕ ℕ) : bool :=
(match next with -- to start the walk we need to get some initial key
| (smap.empty _) := tt
| (smap.leaf k v _ _) := walk k next v (next.size - 1)
| (smap.node k v _ _) :=  walk k next v (next.size - 1)
end)

-- for any two elements we can use next some finite number of times to get from the first to the second
def cycle_prop (next : tmap ℕ ℕ) := next.forall (λ u, next.forall (λ v, ∃ (n : (fin (next.size))), tmap_apply next u n.val = some v))

structure cycle : Type :=
  (next : tmap ℕ ℕ)
  (is_cyc : is_cycle next = tt)

-- Given the cycle structure we in fact have a cycle
theorem cycle_is_cycle_prop (c : cycle) : cycle_prop (c.next) :=
begin
  induction c,
  unfold cycle_prop,
  sorry
end

def is_cycle_of_set (c : cycle) (t : tset ℕ) : bool :=
  (smap.size (c.next) = t.size) ∧
  (t.forall (λ v, c.next.contains_key v))

-- checks that α σ (x, y) = (y, z)
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

--def cycles := 

--end combinatorial_map
