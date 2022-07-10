import .graph
import .tree_set
--import .graph

--namespace combinatorial_map
open tree_set

-- To bo moved to a different file

-- Apply the tmap next n times to some starting parameter
--def tmap_apply_aux {α : Type} [linear_order α] (next : tmap α α) : α → ℕ → option α
def tmap_apply {α : Type} [linear_order α] (next : tmap α α) : α → ℕ → option α
| x 0 := some x
| x (n + 1) := 
  (match next.val_at x with
  | none := none
  | some a := tmap_apply a n
  end)

def tmap_apply_suc {α : Type} [linear_order α] (next : tmap α α) {n : ℕ} {src dst : α} 
  (h : tmap_apply next src n = some dst) : tmap_apply next src (n + 1) = tmap_apply next dst 1 :=
begin
  induction n generalizing src,
  simp [tmap_apply],
  simp [tmap_apply] at h,
  rewrite h,
  simp [tmap_apply] at h,
  simp [tmap_apply],
  cases (next.val_at src),
  simp [tmap_apply._match_1] at h,
  apply false.elim h,
  simp [tmap_apply._match_1],
  simp [tmap_apply._match_1] at h,
  have h' := n_ih h,
  simp [tmap_apply] at h',
  apply h',
end
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
  cur ≠ dst ∧
  (match next.val_at cur with
  | none := ff
  | some val := walk val n 
  end : bool)
def map_next_is (next : tmap ℕ ℕ) (src dst : ℕ) : Prop :=
  next.val_at src = some dst


inductive map_path (next : tmap ℕ ℕ) : ℕ → ℕ → Type
| source (src : ℕ)  :  map_path src src
| extend {src dst dst' : ℕ} (p : map_path src dst) (can_extend : map_next_is next dst dst') : map_path src dst'

def in_path (next : tmap ℕ ℕ) (x : ℕ) : 
  Π {src dst : ℕ}, map_path next src dst → Prop
| _ _ (map_path.source src) := src = x
| src dst' (map_path.extend p can_extend) := dst' = x ∨ in_path p

def end_unique {next : tmap ℕ ℕ} : Π {src dst : ℕ}, map_path next src dst → Prop 
| _ _ (map_path.source src) := true
| src dst' (map_path.extend p can_extend) := ¬ (in_path next dst' p)

def map_path_append {next : tmap ℕ ℕ} : Π {src dst src' dst'}, 
  map_path next src dst → map_path next src' dst' → map_next_is next dst src' → 
  map_path next src dst'
| src dst .(src') .(_) p (map_path.source src') can_extend := map_path.extend p can_extend
| src dst src' dst' p (map_path.extend p' can_extend') can_extend := 
  let p'' := map_path_append p p' can_extend in 
  map_path.extend p'' can_extend'
def map_path.size {next : tmap ℕ ℕ} : Π {src dst : ℕ}, Π (p : map_path next src dst), ℕ
| src dst (map_path.source .(src)) := 0
| src dst (map_path.extend p' can_extend) := p'.size + 1
def map_path_index {next : tmap ℕ ℕ} : Π {src dst : ℕ}, Π (x : ℕ), Π (p : map_path next src dst), 
  in_path next x p → ℕ 
| src dst x (map_path.source .(src)) x_in_p := 0
| src dst x p@(map_path.extend p' can_extend) x_in_p := 
  decidable.cases_on (eq.decidable dst x) 
    (λ dst_neq_x, 
      let x_in_p' : in_path next x p' :=
        begin
          simp [in_path] at x_in_p,
          cases x_in_p with dst_eq_x x_in_p',
            apply false.elim (dst_neq_x dst_eq_x),
          apply x_in_p'
        end
      in
      map_path_index x p' x_in_p'
    ) 
    (λ x_eq_dst, p.size) 
/-
theorem map_path_index_lte_map_size {next : tmap ℕ ℕ} : Π {src dst : ℕ}, Π {x : ℕ}, 
  Π (p : map_path next src dst), Π (x_in_p : in_path next x p), map_path_index x p x_in_p ≤ p.size :=
begin
  intros src dst x p x_in_p,
  induction n with n generalizing dst,
    cases p,
    simp [map_path_index],
  cases p,
  simp [map_path_index],
  cases h' : (eq.decidable dst x),
    simp,
    have x_in_p_p : in_path next x p_p,
      simp [in_path] at x_in_p,
      cases x_in_p with dst_eq_x x_in_p_p,
        apply false.elim (h dst_eq_x),
      apply x_in_p_p,
    have h'' := n_ih p_p x_in_p_p,
    apply le_trans,
      apply h'',
      apply nat.le_succ,
    simp,
end
-/
def src_to_elem {next : tmap ℕ ℕ} : Π {src dst x : ℕ}, Π (p : map_path next src dst), 
  Π (x_in_p : in_path next x p), map_path next src x 
| src dst x p@(map_path.source .(src)) x_in_p := 
  let src_eq_x : src = x :=
    begin
      simp [in_path] at x_in_p,     
      assumption
    end
  in
  @eq.rec_on _ _ (λ x, map_path next src x) _ src_eq_x p
| src dst x p@(map_path.extend p' can_extend) x_in_p := 
  decidable.cases_on (eq.decidable dst x) 
  (λ dst_neq_x, 
    let x_in_p' : in_path next x p' :=
      begin
        simp [in_path] at x_in_p,
        cases x_in_p with dst_eq_x x_in_p',
          apply false.elim (dst_neq_x dst_eq_x),
        apply x_in_p',
      end
    in 
    let p'_to_x := src_to_elem p' x_in_p' in 
    let h : map_path_index x p' x_in_p' = map_path_index x (p'.extend can_extend) x_in_p :=
      begin
        simp [map_path_index], 
        cases h' : (eq.decidable dst x),
          simp,
        apply false.elim (dst_neq_x h),
      end
    in
    eq.rec_on h p'_to_x) 
  (λ dst_eq_x, 
  @eq.rec_on _ _ (λ y, map_path next src y) _ dst_eq_x p)
/-
def elem_to_dst {next : tmap ℕ ℕ} : Π {n src dst x : ℕ}, Π (p : map_path next n src dst),
  Π (x_in_p : in_path next x p), map_path next (n - map_path_index x p x_in_p) x dst 
| 0 src dst x p@(map_path.source .(src)) x_in_p := (
    let src_eq_x : src = x := 
      begin
        simp [in_path] at x_in_p,
        apply x_in_p,
      end
    in
    let h : 0 = 0 - map_path_index x (map_path.source src) x_in_p := 
      begin
        simp [map_path_index],
      end
    in 
    let p' : map_path next (0 - map_path_index x p x_in_p) src src := eq.rec_on h p in
    @eq.rec_on _ _ (λ y, map_path next (0 - map_path_index x p x_in_p) y src) _ src_eq_x p'
  )
| (n + 1) src dst x p@(map_path.extend p' can_extend) x_in_p := (
    decidable.cases_on (eq.decidable dst x)
    (λ dst_neq_x, 
      let x_in_p' : in_path next x p' :=
        begin
          simp [in_path] at x_in_p,
          cases x_in_p with dst_eq_x x_in_p',
            apply false.elim (dst_neq_x dst_eq_x),
          apply x_in_p',
        end
      in
      let elem_to_dst' := elem_to_dst p' x_in_p' in 
      let p'' := map_path.extend elem_to_dst' can_extend in
      let h : n - (map_path_index x p' x_in_p') + 1 = n + 1 - map_path_index x p x_in_p :=
        begin
          simp [map_path_index],
          cases h' : (eq.decidable dst x),
            simp,
            rw add_comm,
            rw ←(nat.add_sub_assoc (map_path_index_lte_map_size p' x_in_p')),
            have h'' : 1 + n - map_path_index x p' x_in_p' = n + 1 - map_path_index x p' x_in_p', 
              apply congr_arg (λ y, y - map_path_index x p' x_in_p'),
              ring,
            rw h'',
            apply false.elim (dst_neq_x h),
        end,
      in
      h.rec_on p''
    )
    (λ dst_eq_x, sorry)
  )
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
theorem path_gives_applications {next : tmap ℕ ℕ} {src dst : ℕ} : Π (p : map_path next src dst), 
  tmap_apply next src (p.size) = some dst :=
begin
  intro p,
  induction p,
    simp [tmap_apply, map_path.size],
  --simp [tmap_apply, map_path.size],
  have h := tmap_apply_suc next p_ih,
  simp [map_path.size],
  rw h,
  simp [tmap_apply],
  unfold map_next_is at p_can_extend,
  rw p_can_extend,
  simp [tmap_apply._match_1],
end
def val_not_in_path_to_dst_neq_val {next : tmap ℕ ℕ} {src dst val : ℕ} (p : map_path next src dst)
  (val_not_in_path : ¬ (in_path next val p)) : dst ≠ val :=
begin
  intro dst_eq_val,
  cases p,
    simp [in_path] at val_not_in_path,
    apply false.elim (val_not_in_path dst_eq_val),
    simp [in_path] at val_not_in_path,
    apply false.elim (val_not_in_path (or.inl dst_eq_val)),
end
def extend_map_path {next : tmap ℕ ℕ} : Π {src dst src' : ℕ}, 
   Π (p : map_path next src dst), Π (can_extend : map_next_is next src' src), 
  map_path next src' dst 
| src dst src' p@(map_path.source _) can_extend := 
  map_path.extend (map_path.source src') can_extend
| src dst src' (map_path.extend path can_extend') can_extend := 
  map_path.extend (extend_map_path path can_extend) can_extend'

theorem extend_map_path_size {next : tmap ℕ ℕ} {n src dst src' : ℕ} (p : map_path next src dst)
  (can_extend : map_next_is next src' src) (p_size : p.size = n) : (extend_map_path p can_extend).size = n + 1 :=
begin
  induction p generalizing n, 
    simp [map_path.size] at p_size,
    simp [extend_map_path, map_path.size],
    apply eq.symm,
    assumption,
  simp [map_path.size, extend_map_path],
  simp [map_path.size] at p_size,
  cases n,
    simp at p_size,
    apply false.elim p_size,
  injection p_size with p_p_size,
  apply p_ih can_extend p_p_size,
end
-- If we extend a map_path from the left an element is in the map if it's in eleement we are adding
-- or if it is in the rest of the map
def in_extend_path {next : tmap ℕ ℕ} {src dst src' x : ℕ} :
  Π (p' : map_path next src dst), Π (can_extend : map_next_is next src' src), 
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
def unique_end_extend {next : tmap ℕ ℕ} {src dst src' : ℕ} : 
  Π (p' : map_path next src dst), Π (can_extend : map_next_is next src' src), 
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
def walk_src_next {next : tmap ℕ ℕ} : Π {n src dst : ℕ}, Π (val_opt : option ℕ), 
   next.val_at src = val_opt → walk dst next src (n + 1) → ℕ
| n src dst none h walk_cond := (
    let ⟨src_neq_dst, walk_cond'⟩ := (to_bool_iff _).mp walk_cond in
    let walk_cond'_false : false :=
      begin
        rw h at walk_cond',
        simp [walk._match_1] at walk_cond',
        apply walk_cond',
      end
    in
    false.elim walk_cond'_false
  )
| n src dst (some val) p walk_cond := val
theorem walk_src_next_is_next {next : tmap ℕ ℕ} : Π {n src dst : ℕ}, Π (val_opt : option ℕ),
  Π (h : next.val_at src = val_opt), Π (walk_cond : walk dst next src (n + 1)),
  next.val_at src = some (@walk_src_next next n src dst val_opt h walk_cond) :=
begin
  intros n src dst val_opt h walk_cond, 
  cases val_opt,
    have h', from (to_bool_iff _).mp walk_cond, 
    have walk_cond', from h'.right,
    rw h at walk_cond',
    simp [walk._match_1] at walk_cond',
    apply false.elim walk_cond',
  simp [walk_src_next],
  apply h,
end

def walk_to_path {next : tmap ℕ ℕ} : Π {n src dst : ℕ}, walk dst next src n = tt → map_path next src dst 
| 0 src dst walk_cond := (
    let src_eq_dst : src = dst := eq.symm ((to_bool_iff _).mp walk_cond) in 
    let p : map_path next src src := map_path.source src in
    src_eq_dst.rec p
  )
| (n + 1) src dst walk_cond := (
    let src_neq_dst :  src ≠ dst := 
      begin
        have h, from ((to_bool_iff _).mp) walk_cond,
        apply h.left,
      end
    in
    let val_opt := next.val_at src in
    let val_opt_eq_next : next.val_at src = val_opt := rfl in
    let val := walk_src_next val_opt val_opt_eq_next walk_cond in
    let val_is_next := walk_src_next_is_next val_opt val_opt_eq_next walk_cond in
    let p' : map_path next val dst := (
        walk_to_path 
        (begin 
          have walk_cond', from ((to_bool_iff _).mp walk_cond).right,
          rw val_is_next at walk_cond',
          simp [walk._match_1] at walk_cond',
          apply walk_cond',
        end)
      )
    in
    extend_map_path p' val_is_next
  )
theorem walk_to_path_size {next : tmap ℕ ℕ} {n src dst : ℕ} (walk_cond : walk dst next src n = tt) :
  (walk_to_path walk_cond).size = n :=
begin
  induction n generalizing src,
  simp [walk_to_path, map_path.size],
  have src_eq_dst : src = dst, from eq.symm ((to_bool_iff _).mp walk_cond), 
  subst src_eq_dst,
  simp [map_path.size],
  simp [walk_to_path],
  apply extend_map_path_size,
  apply n_ih, 
end
theorem walk_to_path_end_unique {next : tmap ℕ ℕ} {n src dst : ℕ} (walk_cond : walk dst next src n) :
  end_unique (walk_to_path walk_cond) :=
begin
  induction n generalizing src,
    have h := walk_to_path_size walk_cond,
    cases (walk_to_path walk_cond),
    simp [end_unique],
    simp [map_path.size] at h,
    apply false.elim h,
  simp [walk_to_path],
  simp [walk] at walk_cond,
  have walk_cond' := walk_cond.right,
  have src_neq_dst := (to_bool_iff _).mpr walk_cond.left,
  simp at src_neq_dst,
  apply unique_end_extend,
  intro dst_eq_src,
  apply false.elim (src_neq_dst (eq.symm dst_eq_src)),
  apply n_ih,
end

def next_of_extended_in_path {next : tmap ℕ ℕ} : Π {x src dst dst' : ℕ}, 
  Π (p : map_path next src dst), Π (can_extend : map_next_is next dst dst'), 
  in_path next x p → ∃ y : ℕ, next.val_at x = some y ∧ in_path next y (map_path.extend p can_extend) :=
begin
  intros x src dst dst' p can_extend in_p,
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

def end_unique_for_smaller {next : tmap ℕ ℕ} : Π {src dst dst' : ℕ},
  Π {p : map_path next src dst}, Π {can_extend : map_next_is next dst dst'},
  end_unique (map_path.extend p can_extend) → end_unique p :=
begin
  intros src dst dst' p can_extend has_end_unique,
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

def map_path_smaller_map : Π {next : tmap ℕ ℕ}, Π {x src dst : ℕ},
  Π (p : map_path next src dst), Π (h : next.contains_key x), ¬ (in_path next x p) → 
  map_path (tmap.remove x next h) src dst
| next x src dst (map_path.source .(src)) h x_nin_p := map_path.source src
| next x src dst p@(@map_path.extend ._ ._ dst' ._ p' can_extend) h x_nin_p := (
  have p'.size < p.size := by simp [map_path.size], -- to help the equation compiler
  let x_nin_p' : ¬(in_path next x p') := 
    begin
      simp [in_path] at x_nin_p,
      intro x_in_p',
      apply false.elim (x_nin_p (or.inr x_in_p')),
    end
  in
  let p'_smaller := map_path_smaller_map p' h x_nin_p' in
  let dst'_in_map := key_in_map_iff_evals dst' dst can_extend in
  let dst'_neq_x : dst' ≠ x := 
    begin
      simp [in_path] at x_nin_p,
      have x_nin_p' : ¬ (in_path next x p'),
        intro x_in_p',
        apply false.elim (x_nin_p (or.inr x_in_p')),
      exact val_not_in_path_to_dst_neq_val p' x_nin_p',
    end
  in
  let dst_val_eq := remove_preserves_values x next h dst' dst'_in_map dst'_neq_x in
  let can_extend' : map_next_is (tmap.remove x next h) dst' dst := 
    begin
      unfold map_next_is,
      rw dst_val_eq,
      unfold map_next_is at can_extend,
      exact can_extend,
    end
  in
  map_path.extend p'_smaller can_extend'
  )
using_well_founded {rel_tac := λ _ _ , 
  `[exact ⟨_, measure_wf (λ ⟨_, _, _, _, p, _, _⟩, p.size)⟩]} 

theorem map_path_smaller_map_size {next : tmap ℕ ℕ} {x src dst : ℕ}
  (p : map_path next src dst) (h : next.contains_key x) (x_nin_p : ¬ (in_path next x p)) :
  p.size = (map_path_smaller_map p h x_nin_p).size :=
begin
  induction p,
    simp [map_path.size, map_path_smaller_map],
  simp [map_path.size, map_path_smaller_map],
  apply p_ih,
end
theorem map_path_smaller_elem {next : tmap ℕ ℕ} {x src dst : ℕ} 
  (p : map_path next src dst) (h : next.contains_key x) (x_nin_p : ¬ (in_path next x p)) :
  ∀ y, in_path next y p ↔ in_path (tmap.remove x next h) y (map_path_smaller_map p h x_nin_p) :=
begin
  intro y,
  induction p,
    simp [in_path, map_path_smaller_map],
  simp [in_path, map_path_smaller_map],
  have x_nin_p_p : ¬ (in_path next x p_p),
    intro x_in_p_p,
    apply false.elim (x_nin_p (or.inr x_in_p_p)),
  split,
  -- →
  intro y_in_p,
  cases y_in_p with p_dst'_eq_y y_in_p_p,
    apply or.inl p_dst'_eq_y,
  apply or.inr,
  apply (p_ih x_nin_p_p).mp,
  apply y_in_p_p,
  -- ←
  intro h,
  cases h with p_dst'_eq_y y_in_p',
    apply or.inl p_dst'_eq_y,
  apply or.inr,
  apply (p_ih x_nin_p_p).mpr, 
  apply y_in_p',
end
theorem map_path_smaller_map_end_unique {next : tmap ℕ ℕ} {x src dst : ℕ}
  (p : map_path next src dst) (p_end_unique : end_unique p) (h : next.contains_key x) 
  (x_nin_p : ¬ (in_path next x p)) : end_unique (map_path_smaller_map p h x_nin_p) :=
begin
  induction p,
    simp [end_unique, map_path_smaller_map],
  have p_p_end_unique : end_unique p_p, from end_unique_for_smaller p_end_unique,
  have x_nin_p_p : ¬ (in_path next x p_p),
    simp [in_path] at x_nin_p,
    intro x_in_p_p,
    apply false.elim (x_nin_p (or.inr x_in_p_p)),
  have smaller_end_unique := p_ih p_p_end_unique x_nin_p_p,
  simp [end_unique, map_path_smaller_map],
  intro p_dst'_in_path,
  have p_dst'_in_p_p := (map_path_smaller_elem p_p h x_nin_p_p p_dst').mpr p_dst'_in_path,
  simp [end_unique] at p_end_unique,
  apply false.elim (p_end_unique p_dst'_in_p_p),
end

def path_of_length_size_all_keys {src : ℕ} : Π {dst : ℕ}, Π {next : tmap ℕ ℕ}, 
  Π (p : map_path next src dst), (end_unique p) → next.contains_key dst → next.size = p.size + 1 → 
  ∀ (x : ℕ), next.contains_key x → in_path next x p :=
begin
  intros dst next p,
  induction p_size : (p.size) generalizing p dst next,
    -- case: 0
    intros p_end_unique dst_in_map size_cond x x_in_map,
    simp at size_cond,
    have h := tmap_size_1_implies_all_els_eq size_cond,
    cases p,
    have x_eq_src := h x src x_in_map dst_in_map,
    rewrite x_eq_src,
    simp [in_path],
    simp [map_path.size] at p_size,
    apply false.elim p_size,
    -- case: n + 1
    intros p_end_unique dst_in_map size_cond x x_in_map,
    cases p,
      simp [map_path.size] at p_size,
      injection p_size,
    have p_p_end_unique := end_unique_for_smaller p_end_unique,
    simp [in_path],
    by_cases (dst = x),
      apply or.inl h,
    apply or.inr,
    simp [end_unique] at p_end_unique,
    have p' := map_path_smaller_map p_p dst_in_map p_end_unique,
    have p'_end_unique := map_path_smaller_map_end_unique p_p p_p_end_unique dst_in_map p_end_unique,
    have p'_elem_cond := map_path_smaller_elem p_p dst_in_map p_end_unique,
    have p_dst_in_next := key_in_map_iff_evals p_dst dst p_can_extend, 
    have dst_neq_p_dst := val_not_in_path_to_dst_neq_val p_p p_end_unique,
    have p_dst_neq_dst := λ x, dst_neq_p_dst (eq.symm x),
    have p_dst_in_new_map := 
      remove_preserves_other_keys dst next dst_in_map p_dst p_dst_in_next p_dst_neq_dst,
    have new_map_size := remove_size dst next dst_in_map,
    simp [size_cond] at new_map_size,
    have x_in_new_map := remove_preserves_other_keys dst next dst_in_map x x_in_map h,
    simp [map_path.size] at p_size,
    injection p_size with p'_size,
    rw (map_path_smaller_map_size p_p dst_in_map p_end_unique) at p'_size, 
    have x_in_p' := 
      ih
        (map_path_smaller_map p_p dst_in_map p_end_unique) 
        p'_size 
        p'_end_unique 
        p_dst_in_new_map 
        new_map_size 
        x 
        x_in_new_map,
    apply (p'_elem_cond x).mpr,
    apply x_in_p',
end

