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

def tmap_add {α : Type} [linear_order α] {β : Type} :
  tmap α β → α → β → tmap α β := sorry

def tmap_add_list {α : Type} [linear_order α] {β : Type} : 
  list (α × β) → tmap α β → tmap α β 
| [] next := next
| ((k , v) :: ls) next := tmap_add_list ls (tmap_add next k v)
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
  sorry
end

def is_cycle_of_set (c : cycle) (t : tset ℕ) : bool :=
  (smap.size (c.next) = t.size) ∧
  (t.forall (λ v, c.next.contains_key v))

--def is_cycle_of_list (f : ℕ → ℕ) : list ℕ → bool 
--| [] := tt
-- | l@(x :: xs) := walk_with x c.next l x
def face_next_is (σ : tmap ℕ cycle) (x y z : ℕ) : bool :=
(match σ.val_at x with
| none := ff
| some c := (
  match c.next.val_at y with
  | none := ff
  | some val := z = val
  end
  )
end)

def is_list_of_face_aux (σ : tmap ℕ cycle) (fst : ℕ) (snd : ℕ) : list ℕ → bool
| [] := tt
| (x :: []) := face_next_is σ x fst snd
| (x :: y :: []) := face_next_is σ x y fst
| (x :: l@(y :: z :: xs)) := face_next_is σ x y z ∧ is_list_of_face_aux l


def is_list_of_face (σ : tmap ℕ cycle) : list ℕ → bool
| [] := ff -- empty lists shouldn't be present
| (x :: []) := (
  match σ.val_at x with
  | none := ff
  | some c := c.next.size = 0 -- list has one element only if vertex is isolated
  end
  )
| l@(x :: y :: xs) := is_list_of_face_aux σ x y l


def neighbours_add : tmap ℕ (tset ℕ) → Edge → tmap ℕ (tset ℕ) := sorry

def neighbours_aux [lo : linear_order Edge] : (tmap ℕ (tset ℕ)) → Π {low high : bounded Edge}, Π {p : low < high},
  @stree Edge lo low high p → tmap ℕ (tset ℕ)
| (neighbours_acc) _ _ _ (stree.empty _) := neighbours_acc
| neighbours_acc _ _ _ (stree.leaf x _ _) := neighbours_add neighbours_acc x
| neighbours_acc _ _ _ (stree.node x l r) := (
  let new_acc := neighbours_aux neighbours_acc l in 
  let final_acc := neighbours_aux new_acc r in
  neighbours_add final_acc x
)

def neighbours (G : simple_irreflexive_graph) : tmap ℕ (tset ℕ) := 
  neighbours_aux (@smap.empty ℕ (tset ℕ) _ bounded.bottom bounded.top true.intro) G.edges
 
def smap.forall_items (p : (ℕ → (cycle) → bool)) :
  ∀ {low high : bounded ℕ} {b : low < high} (t : smap ℕ (cycle) b) , bool := sorry

def graph_rotation_consistent (G : simple_irreflexive_graph) (v : ℕ) (c : cycle) : bool :=
  let ns : option (tset ℕ) := (neighbours G).val_at v in
  (match ns with
  | none := ff
  | some val := is_cycle_of_set c val
  end : bool)

--def face_map (σ : tmap ℕ cycle) : tmap ℕ cycle 

structure combinatorial_map (G : simple_irreflexive_graph) : Type :=
  (σ : tmap ℕ cycle)
  (σ_G_consistent : smap.forall_items (graph_rotation_consistent G) σ = tt)
  (faces : list (list ℕ))
  (composition_faces_consistent : faces.all (is_list_of_face σ)) -- shows that every face is in fact the face of α ∘ σ
  --shows that every face is present by checking that the correct number of edges is present
  (num_of_edges : 
    let empty_map : tmap ℕ ℕ := smap.empty (by trivial) in
    -- here add doesn't work as intended
    let combined_edges : tmap ℕ ℕ := sorry in --faces.foldr tmap_add_list empty_map in
    (smap.size combined_edges) = 2 * (simple_irreflexive_graph.edge_size G)
  )
  
  -- might still require checking if list actually contains edges

--def cycles := 

--end combinatorial_map
