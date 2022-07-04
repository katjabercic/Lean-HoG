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

-- remove key from tmap
def tmap.remove {α β : Type} [linear_order α] (key : α) : Π (m : tmap α β), m.contains_key key → tmap α β 
  := sorry

-- removal of key decreases size by 1
theorem remove_size {α β : Type} [linear_order α] (key : α) : Π (m : tmap α β), Π (p : m.contains_key key),
  smap.size (tmap.remove key m p) = m.size - 1 := sorry

theorem remove_preserves_other_keys {α β : Type} [linear_order α] (key : α) : 
  Π (m : tmap α β), Π (p : m.contains_key key), ∀ x, m.contains_key x → key ≠ x → 
    (tmap.remove key m p).contains_key x := sorry
theorem remove_preserves_values {α β : Type} [linear_order α] (key : α) : 
  Π (m : tmap α β), Π (p : m.contains_key key), ∀ x, m.contains_key x → x ≠ key → 
  (tmap.remove key m p).val_at x = m.val_at x := sorry
theorem key_in_map_iff_evals {α β : Type} [linear_order α] {next : tmap α β} (key : α) (val : β) :
  next.val_at key = some val → next.contains_key key := sorry
set_option trace.check true
theorem tmap_size_1_implies_all_els_eq {α β : Type} [linear_order α] : Π {next : tmap α β}, 
  next.size = 1 → ∀ (x y : α), next.contains_key x → next.contains_key y → x = y :=
sorry
--set_option 
/-
  end of things to be moved
-/
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

--end combinatorial_map

def val_not_in_path_to_dst_neq_val {next : tmap ℕ ℕ} {n src dst val : ℕ} (p : map_path next n src dst)
  (val_not_in_path : ¬ (in_path next val p)) : dst ≠ val :=
begin
  intro dst_eq_val,
  cases p,
    simp [in_path] at val_not_in_path,
    apply false.elim (val_not_in_path dst_eq_val),
    simp [in_path] at val_not_in_path,
    apply false.elim (val_not_in_path (or.inl dst_eq_val)),
end
def extend_map_path {next : tmap ℕ ℕ} : Π {n src dst src' : ℕ}, 
   Π (p : map_path next n src dst), Π (can_extend : map_next_is next src' src), 
  map_path next (n + 1) src' dst 
| n src dst src' p@(map_path.source _) can_extend := 
  map_path.extend (map_path.source src') can_extend
| n src dst src' (map_path.extend path can_extend') can_extend := 
  map_path.extend (extend_map_path path can_extend) can_extend'

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
    (walk dst next src n = tt) → ∃ p : map_path next n src dst, end_unique p :=
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
    have p' := n_ih hr',
    cases p' with p' p'_unique,
    split,
    show map_path next n_n.succ src dst, 
    begin
      apply extend_map_path p' h_map
    end,  
    apply unique_end_extend p' h_map hl p'_unique,
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
  Π {p : map_path next n src dst}, Π {can_extend : map_next_is next dst dst'},
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

def path_in_smaller_map : Π {next : tmap ℕ ℕ}, Π {n x src dst : ℕ}, 
  Π (p : map_path next n src dst), end_unique p → Π (h : next.contains_key x), ¬(in_path next x p) →
  ∃ (p' : map_path (tmap.remove x next h) n src dst), end_unique p' ∧ (∀ y, in_path next y p ↔ in_path (tmap.remove x next h) y p') := 
begin 
  intros next n x src dst p p_end_unique h not_in_p,
  induction p,
  split,
  show map_path (tmap.remove x next h) 0 p p, from map_path.source p,
  split,
  simp [end_unique],
  intro y,
  split,
  intro in_p,
  simp [in_path],
  simp [in_path] at in_p,
  apply in_p,
  intro in_p,
  simp [in_path],
  simp [in_path] at in_p,
  apply in_p,
  simp [in_path] at not_in_p,
  have p_dst_neq_x : p_dst' ≠ x := λ p_dst_eq_x, not_in_p (or.inl p_dst_eq_x),
  have not_in_p_p : ¬ (in_path next x p_p) := λ in_p_p, not_in_p (or.inr in_p_p),
  have p_p_end_unique := end_unique_for_smaller p_end_unique,
    show ℕ, from (n - 1),
  have p_p_in_smaller_map := p_ih p_p_end_unique not_in_p_p,
  cases p_p_in_smaller_map with p' h',
  cases h' with p'_end_unique els_consistent,
  have p_can_extend' : map_next_is (tmap.remove x next h) p_dst p_dst', 
  begin
    unfold map_next_is,
    unfold map_next_is at p_can_extend,
    have p_dst_in_map := key_in_map_iff_evals p_dst p_dst' p_can_extend,
    have x_neq_p_dst := val_not_in_path_to_dst_neq_val p_p not_in_p_p, 
    rewrite remove_preserves_values x next h p_dst p_dst_in_map x_neq_p_dst,
    apply p_can_extend,
  end,
  split,
    show map_path (tmap.remove x next h) (p_n + 1) p_src p_dst', from (map_path.extend p' p_can_extend'),
    split,
      simp [end_unique],
      intro p_dst'_in_p',
      have p_dst'_in_p_p := (els_consistent p_dst').mpr p_dst'_in_p',
      unfold end_unique at p_end_unique,
      apply false.elim (p_end_unique p_dst'_in_p_p),
      intro y, 
      split,
        intro y_in_path,
        simp [in_path],
        simp [in_path] at y_in_path,
        cases y_in_path,
        apply or.inl y_in_path,
        apply or.inr ((els_consistent y).mp y_in_path),
        intro y_in_path,
        simp [in_path],
        simp [in_path] at y_in_path,
        cases y_in_path,
        apply or.inl y_in_path,
        apply or.inr ((els_consistent y).mpr y_in_path),
end
def path_of_length_size_all_keys {src : ℕ} : Π {n dst : ℕ}, Π {next : tmap ℕ ℕ}, 
  Π (p : map_path next n src dst), (end_unique p) → next.contains_key dst → next.size = n + 1 → 
  ∀ (x : ℕ), next.contains_key x → in_path next x p :=
begin
  intros n,
  induction n,
    -- case: 0
    intros dst next p p_end_unique dst_in_map size_cond x x_in_map,
    simp at size_cond,
    have h := tmap_size_1_implies_all_els_eq size_cond,
    cases p,
    have x_eq_src := h x src x_in_map dst_in_map,
    rewrite x_eq_src,
    simp [in_path],
    -- case: n + 1
    intros dst next p p_end_unique dst_in_map size_cond x x_in_map,
    cases p,
    have p_p_end_unique := end_unique_for_smaller p_end_unique,
      show ℕ, from n_n,
    simp [in_path],
    by_cases (dst = x),
      apply or.inl h,
    apply or.inr,
    simp [end_unique] at p_end_unique,
    have p'_exists := path_in_smaller_map p_p p_p_end_unique dst_in_map p_end_unique,
    cases p'_exists with p' p'_cond,
    cases p'_cond with p'_end_unique p'_elem_cond,
    have p_dst_in_next := key_in_map_iff_evals p_dst dst p_can_extend, 
    have dst_neq_p_dst := val_not_in_path_to_dst_neq_val p_p p_end_unique,
    have p_dst_neq_dst := λ x, dst_neq_p_dst (eq.symm x),
    have p_dst_in_new_map := 
      remove_preserves_other_keys dst next dst_in_map p_dst p_dst_in_next p_dst_neq_dst,
    have new_map_size := remove_size dst next dst_in_map,
    simp [size_cond] at new_map_size,
    have x_in_new_map := remove_preserves_other_keys dst next dst_in_map x x_in_map h,
    have x_in_p' := n_ih p' p'_end_unique p_dst_in_new_map new_map_size x x_in_new_map,
    apply (p'_elem_cond x).mpr,
    apply x_in_p',
end

