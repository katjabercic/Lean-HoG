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
def walk (dst : ℕ) (next : tmap ℕ ℕ) : ℕ → ℕ → bool
| cur 0 := dst = cur
| cur (n + 1) := 
  dst ≠ cur ∧
  (match next.val_at cur with
  | none := ff
  | some val := walk val n 
  end : bool)
def map_next_is (next : tmap ℕ ℕ) (src dst : ℕ) : Prop :=
  next.val_at src = some dst


inductive map_path (next : tmap ℕ ℕ) : ℕ → ℕ → ℕ → Type
| source (src : ℕ)  :  map_path 0 src src
| extend {n src dst dst' : ℕ} (p : map_path n src dst) (can_extend : map_next_is next dst dst') : map_path (n + 1) src dst'

def in_path (next : tmap ℕ ℕ) (x : ℕ) : 
  Π {n src dst : ℕ}, map_path next n src dst → Prop
| n _ _ (map_path.source src) := src = x
| n src dst' (map_path.extend p can_extend) := dst' = x ∨ in_path p

def end_unique {next : tmap ℕ ℕ} : Π {src dst n : ℕ}, map_path next n src dst → Prop 
| _ _ n (map_path.source src) := true
| src dst' n (map_path.extend p can_extend) := ¬ (in_path next dst' p)

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
def extend_map_path {next : tmap ℕ ℕ} : Π {n src dst src' : ℕ}, 
   Π (p : map_path next n src dst), Π (can_extend : map_next_is next src' src), 
  map_path next (n + 1) src' dst 
| n src dst src' p@(map_path.source _) can_extend := 
  map_path.extend (map_path.source src') can_extend
| n src dst src' (map_path.extend path can_extend') can_extend := 
  map_path.extend (extend_map_path path can_extend) can_extend'

/-
def walk_path {next : tmap ℕ ℕ} {n src dst : ℕ} : walk dst next src n = tt → ∃ p : map_path next n src dst, end_unique p :=
begin
  intro walk_true,
  induction n generalizing src,
  -- the n = 0 case
  unfold walk at walk_true,
  have src_eq_dst := (to_bool_iff _).mp walk_true,
  split,
  show map_path next 0 src dst, by {rewrite src_eq_dst, apply map_path.source src},
  obviously,
  -- the n + 1 case
  unfold walk at walk_true,
  have walk_true := (to_bool_iff _).mp walk_true,
  cases walk_true with dst_neq_src walk_cont',
  have walk_cont := (to_bool_iff _).mpr walk_cont',
  simp at walk_cont,
  -- consider cases where map evaluates to none and when map evaluates to some val
  -- case : none
  cases map_eval : (tmap.val_at src next),
  rewrite map_eval at walk_cont,
  simp [walk._match_1] at walk_cont,
  apply false.elim walk_cont, -- so the map cannot evaluate to none
  -- case : some val
  rewrite map_eval at walk_cont,
  simp [walk._match_1] at walk_cont,
  show map_path next n_n.succ src dst,
  begin
    have p' := n_ih walk_cont,
    cases p',
  end

end
-/
-- If we extend a map_path from the left an element is in the map if it's in eleement we are adding
-- or if it is in the rest of the map
def in_extend_path {next : tmap ℕ ℕ} {n src dst src' x : ℕ} :
  Π (p' : map_path next n src dst), Π (can_extend : map_next_is next src' src), 
  in_path next x (extend_map_path p' can_extend) → in_path next x p' ∨ x = src' :=
begin
  intros p' can_extend in_p,
  induction p',
  simp [extend_map_path, in_path] at in_p,
  cases in_p,
  simp [in_path],
  apply or.inl,
  apply in_p,
  apply or.inr,
  apply (eq.symm in_p),
  simp [in_path, extend_map_path] at in_p,
  simp [in_path, extend_map_path],
  cases in_p,
  apply or.inl,
  apply or.inl,
  apply in_p,
  have h := p'_ih can_extend in_p,
  cases h,
  apply or.inl,
  apply or.inr,
  apply h,
  apply or.inr,
  apply h,
end
-- if the new source isn't equal to the destination and the old map
-- has a unique end the whole map has a unique end
def unique_end_extend {next : tmap ℕ ℕ} {n src dst src' : ℕ} : 
  Π (p' : map_path next n src dst), Π (can_extend : map_next_is next src' src), 
  dst ≠ src' → end_unique p' → end_unique (extend_map_path p' can_extend ) :=
begin
  intros p' next_is dst_neq_src' end_uniq,
  cases p' with p'' p''_can_extend,
  -- the path is just the source case
  simp [extend_map_path, end_unique],
  intro in_p'',
  simp [in_path] at in_p'',
  apply dst_neq_src' (eq.symm in_p''),
  -- the case where path is of the map_path.extend form
  simp [extend_map_path, end_unique],
  intro in_p,
  unfold end_unique at end_uniq,
  have h := in_extend_path p'_p next_is in_p,
  cases h,
  apply false.elim (end_uniq h),
  apply false.elim (dst_neq_src' h),
end
/- 
  given a walk of length n we can get a map_path of length n with 
  the same source and destination. 

  Additionaly said path has a unique ending.
-/
def walk_gives_path {next : tmap ℕ ℕ} {n src dst : ℕ} : 
  (walk dst next src n = tt) → {p : map_path next n src dst // end_unique p} :=
begin
  intro h,
  induction n generalizing src,
  -- the base case
  unfold walk at h,
  have h' := (to_bool_iff (dst = src)).mp h,
  split,
  show map_path next 0 src dst, by {rewrite h', apply map_path.source src},
  show end_unique _, by {obviously},
  -- the n + 1 case
  unfold walk at h,
  have h' := (to_bool_iff _).mp h,
  cases h' with hl hr,
  have hr' := (to_bool_iff _).mpr hr,
  simp at hr',
  cases h_map : (tmap.val_at src next),
  rewrite h_map at hr',
  unfold walk._match_1 at hr',
  simp at hr',
  apply false.elim hr',
  rewrite h_map at hr',
  unfold walk._match_1 at hr',
  split,
  show map_path next n_n.succ src dst, 
  begin
    have p' := n_ih hr',
    cases p' with p' p'_unique,
    apply extend_map_path p' h_map
  end,  
  cases n_ih hr' with p' p'_unique,
  simp,
  show end_unique (extend_map_path p' h_map), 
    from unique_end_extend p' h_map hl p'_unique,
end

def next_of_extended_in_path {next : tmap ℕ ℕ} : Π {x n src dst dst' : ℕ}, 
  Π (p : map_path next n src dst), Π (can_extend : map_next_is next dst dst'), 
  in_path next x p → ∃ y : ℕ, next.val_at x = some y ∧ in_path next y (map_path.extend p can_extend) :=
begin
  intros x n src dst dst' p can_extend in_p,
  induction p generalizing dst',
  simp [in_path] at in_p,
  apply exists.intro,
  show ℕ, from dst',
  apply and.intro,
  rewrite ←in_p,
  apply can_extend,
  simp [in_path],
  cases in_p,
  split,
  show ℕ, from dst',
  rewrite ←in_p, 
  split,
  apply can_extend,
  simp [in_path],
  have h := p_ih in_p p_can_extend,
  cases h with val h,
  split,
  show ℕ, from val,
  split,
  cases h,
  apply h_left,
  unfold in_path,
  cases h,
  simp [in_path] at h_right,
  apply or.inr,
  apply h_right, 
end

def end_unique_for_smaller {next : tmap ℕ ℕ} : Π {x n src dst dst' : ℕ},
  Π (p : map_path next n src dst), Π (can_extend : map_next_is next dst dst'),
  end_unique (map_path.extend p can_extend) → end_unique p :=
begin
  intros x n src dst dst' p can_extend has_end_unique,
  simp [end_unique] at has_end_unique,
  induction p,
  simp [end_unique],
  simp [end_unique],
  intro in_p_p,
  have h := next_of_extended_in_path p_p p_can_extend in_p_p,
  cases h with val h,
  cases h,
  simp [map_next_is] at can_extend,
  rewrite h_left at can_extend,
  injection can_extend with h,
  rewrite h at h_right,
  apply has_end_unique,
  apply h_right,
end

  
/-
inductive map_path (next : tmap ℕ ℕ) : ℕ → ℕ → ℕ → Prop
| source (src : ℕ)  :  map_path 0 src src
| extend {n src dst dst' : ℕ} (p : map_path n src dst) (can_extend : map_next_is next dst dst') : map_path (n + 1) src dst'
open map_path
set_option trace.eqn_compiler.elim_match true
def in_path {next : tmap ℕ ℕ} (x : ℕ) : ∀ {n src dst : ℕ}, map_path next n src dst → Prop 
| _ _ _ (source src) := x = src
|_ src _ (extend p can_extend) := x = src ∨ in_path p
-/
