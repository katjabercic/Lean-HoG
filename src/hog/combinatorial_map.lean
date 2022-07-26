import .graph
import .tree_set
import .map_path
--import .graph

--namespace combinatorial_map
open tree_set
open map_path
-- To bo moved to a different file

lemma list.cons_append_assoc {α : Type} (x : α) (l₁ l₂ : list α) : x :: (l₁ ++ l₂) = (x :: l₁) ++ l₂ :=
begin
  induction l₁,
    simp,
  simp,
end
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
def is_list_of_σα (σ : tmap ℕ cycle) : list ℕ → bool
| [] := tt
| (x :: []) := ff 
| (x :: y :: []) := tt 
| (x :: l@(y :: z :: xs)) := σα_maps σ x y z && is_list_of_σα l
def is_face_of_σα (σ : tmap ℕ cycle) : list ℕ → bool 
| [] := ff 
| (x :: []) := ff
| l@(x :: y :: xs) := is_list_of_σα σ (l ++ [x] ++ [y])
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
def tset.elem_add {α : Type} [linear_order α] (t : tset α) (x y : α) : x = y → (t.add y).elem x
  := sorry
def tset.elem_add_diff {α : Type} [linear_order α] (t : tset α) (x y : α) : 
  x ≠ y → (t.add y).elem x → t.elem x := sorry
def tset.add_preserves {α : Type} [linear_order α] (t : tset α) (x y : α) :
  t.elem x → (t.add y).elem x := sorry
def add_list_to_set_if_unique : tset (lex ℕ ℕ) → list ℕ → option (tset (lex ℕ ℕ))
| acc [] := some acc
| acc (x :: []) := some acc
| acc (x :: y :: xs) := (
    match acc.elem (x, y) with 
    | tt := none
    | ff := add_list_to_set_if_unique (acc.add (x, y)) (y :: xs)
    end
  )

def add_face_to_set_if_unique : tset (lex ℕ ℕ) → list ℕ → option (tset (lex ℕ ℕ))
| acc [] := some acc 
| acc (x :: []) := some acc
| acc l@(x :: y :: xs) := add_list_to_set_if_unique acc (l ++ [x, y])
def faces_unique_edges_aux : tset (lex ℕ ℕ) → list (list ℕ) → option (tset (lex ℕ ℕ)) 
| acc [] := some acc 
| acc (f :: fs) := (
    match add_face_to_set_if_unique acc f with 
    | none := none
    | some acc := faces_unique_edges_aux acc fs
    end
  )
def faces_unique_edges (fs : list (list ℕ)) : bool :=
match (faces_unique_edges_aux (stree.empty true.intro) fs) with
| none := ff
| some acc := tt
end
-- constructs an edge and adds it to a tset Edge
-- takes all pairs of consecuative numbers to generate edges and add them to a tset 
def add_edges_from_face_aux : ℕ → tset (lex ℕ ℕ) → list ℕ → tset (lex ℕ ℕ)
| start es [] := es
| start es (x :: []) :=  es.add (x, start)
| start es (x :: y :: xs) := (add_edges_from_face_aux start es xs).add (x, y)
--def face_map (σ : tmap ℕ cycle) : tmap ℕ cycle 

def add_edges_from_face : tset (lex ℕ ℕ) → list ℕ → tset (lex ℕ ℕ)
| es [] := es 
| es f@(x :: xs) := add_edges_from_face_aux x es f
def add_list_to_set : list ℕ → tset (lex ℕ ℕ) → tset (lex ℕ ℕ)
| [] es := es
| (_ :: []) es := es
| (x :: y :: xs) es := (add_list_to_set (y :: xs) es).add (x, y)

def add_face_to_set : list ℕ → tset (lex ℕ ℕ) → tset (lex ℕ ℕ)
| [] es := es
| (x :: []) es := es
| l@(x :: y :: xs) es := add_list_to_set (l ++ [x] ++ [y]) es
def is_cycle_of_opt (σ : tmap ℕ cycle) (x : ℕ) (t : tset ℕ) : bool :=
(match σ.val_at x with
| none := ff
| some c := is_cycle_of_set c t
end)
def faces_set_from_lst_aux : tset (lex ℕ ℕ) → list (list ℕ) → tset (lex ℕ ℕ)
| acc [] := acc
| acc (f :: fs) := faces_set_from_lst_aux (add_face_to_set f acc) fs
def faces_set_from_lst : list (list ℕ) → tset (lex ℕ ℕ)
| [] := stree.empty true.intro 
| (f :: fs) := add_face_to_set f (faces_set_from_lst fs)

def list_min_edge : list ℕ → lex ℕ ℕ
| [] := (0, 0)
| (x :: []) := (x, x)
| (x :: y :: xs) := min (x, y) (list_min_edge (y :: xs))
def face_min_edge : list ℕ → lex ℕ ℕ
| [] := (0, 0)
| l@(x :: xs) := list_min_edge (l ++ [x])
def faces_ordered : list (list ℕ) → bool
| [] := tt
| (f :: []) := tt
| (f :: f' :: fs) := face_min_edge f < face_min_edge f' ∧ faces_ordered (f' :: fs)
structure combinatorial_map (G : simple_irreflexive_graph) : Type :=
  (σ : tmap ℕ cycle)
  --(σ_G_consistent : smap.forall_items (graph_rotation_consistent G) σ = tt)
  (G_σ_consistent : tmap.forall_items (λ k t, is_cycle_of_opt σ k t) (neighbours G) = tt)
  (σ_keys_neighbour_keys : smap.forall_keys (λ k, (neighbours G).contains_key k) σ)
  (faces : list (list ℕ))
  (composition_faces_consistent : ∀ f, f ∈ faces → (is_face_of_σα σ f)) -- shows that every face is in fact a face of σ ∘ α
  --shows that every face is present by checking that the correct number of edges is present
  (num_of_edges : (faces_set_from_lst faces).size = 2 * (G.edge_size))
  (edges_unique : faces_unique_edges faces = tt)
  --(faces_ord : faces_ordered faces)
  
  -- might still require checking if list actually contains edges
-- σ maps edges to edges with the same source
theorem faces_nonempty {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ f ∈ K.faces, (list.length f) ≠ 0 :=
begin
  intros f f_in_faces,
  intro f_len,
  cases f,
    have h := K.composition_faces_consistent list.nil f_in_faces,
    simp [is_face_of_σα, is_list_of_σα] at h,
    apply h,
  simp [list.length] at f_len,
  apply f_len,
end
def cycle_contains_key_opt (k : ℕ) : option cycle → bool 
| none := ff
| (some c) := c.next.contains_key k
def in_neighbours_opt (G : simple_irreflexive_graph) (x y : ℕ) : Prop :=
(match (neighbours G).val_at x with 
| none := false
| some (x_neigh) := y ∈ x_neigh
end)
def edge_in_face_aux (start : ℕ) : (lex ℕ ℕ) → list ℕ → Prop
| _ [] := false
| x (z :: []) := x = (z, start)
| x (z :: z' :: zs) := x = (z, z') ∨ edge_in_face_aux x (z' :: zs)
def edge_in_list : (lex ℕ ℕ) → list ℕ → Prop 
| e [] := false
| e (x :: []) := false
| e (x :: y :: xs) := e = (x, y) ∨ edge_in_list e (y :: xs)
def edge_in_face : (lex ℕ ℕ) → list ℕ → Prop 
| e [] := false 
| e (x :: []) := false
| e l@(x :: y :: xs) := edge_in_list e (l ++ [x] ++ [y]) 
theorem edge_in_list_iff_in_set (l : list ℕ) : 
  ∀ e, (add_list_to_set l (stree.empty true.intro)).elem e ↔ edge_in_list e l :=
begin
  intro e,
  induction l with x xs,
    split,
    simp [add_list_to_set],
    simp [edge_in_list],
  cases xs with y xs,
    simp [add_list_to_set, edge_in_list],
  simp [add_list_to_set, edge_in_list],
  split,
    intro e_in_extended,
    by_cases h : e = (x, y),
      apply or.inl, assumption,
    let t := add_list_to_set (y :: xs) (stree.empty true.intro),
    have e_in_t := tset.elem_add_diff t e (x, y) h e_in_extended,
    apply or.inr,
    apply l_ih.mp,
    apply e_in_t,
  intro h,
  by_cases h' : e = (x, y),
    apply tset.elem_add,
    apply h',

  apply tset.add_preserves,
  apply l_ih.mpr,
  cases h,
    apply false.elim (h' h),
  exact h,
end
theorem edge_in_added_list (l : list ℕ) (t : tset (lex ℕ ℕ)) (e : lex ℕ ℕ) : 
  (add_list_to_set l t).elem e ↔ edge_in_list e l ∨ t.elem e :=
begin 
  induction l with x xs ,
    simp [add_list_to_set, edge_in_list],
  cases xs with y xs,
    simp [add_list_to_set, edge_in_list],
  simp [add_list_to_set, edge_in_list],
  split,
    intro e_in,
    by_cases h : e = (x, y),
      apply or.inl,
      apply or.inl,
      assumption,
    have e_in' := tset.elem_add_diff (add_list_to_set (y :: xs) t) _ _ h e_in,
    rw or.assoc,
    apply or.inr,
    apply l_ih.mp,
    assumption,
  intro h,
  cases h with h e_elem,
    cases h with e_eq e_in,
      apply tset.elem_add,
      assumption,
    apply tset.add_preserves,
    apply l_ih.mpr,
    apply or.inl,
    assumption,
  apply tset.add_preserves,
  apply l_ih.mpr,
  apply or.inr,
  assumption,
end
theorem edge_in_added_face (f : list ℕ) (t : tset (lex ℕ ℕ)) (e : lex ℕ ℕ) : 
  (add_face_to_set f t).elem e ↔ edge_in_face e f ∨ t.elem e :=
begin
  cases f with x xs,
    simp [add_face_to_set, edge_in_face],
  cases xs with y xs,
    simp [add_face_to_set, edge_in_face],
  apply edge_in_added_list,
end
theorem edge_in_face_iff_in_set (l : list ℕ) : 
  ∀ e, (add_face_to_set l (stree.empty true.intro)).elem e ↔ edge_in_face e l :=
begin
  intro e,
  cases l with x xs,
    simp [add_face_to_set, edge_in_face],
  cases xs with y xs,
    simp [add_face_to_set, edge_in_face],
  apply edge_in_list_iff_in_set,
end
theorem in_faces_set_iff (faces : list (list ℕ)) : 
  ∀ e, (faces_set_from_lst faces).elem e ↔ ∃ f, f ∈ faces ∧ edge_in_face e f :=
begin
  intro e,
  induction faces with f fs,
    simp [faces_set_from_lst, faces_set_from_lst_aux],
  simp [faces_set_from_lst],
  split,
    intro e_in,
    have h := (edge_in_added_face f (faces_set_from_lst fs) e).mp e_in,
    cases h with e_in_f e_in_fs,
    split,
      show list ℕ, from f,
      split,
        apply or.inl,
        refl,
      assumption,
    have exists_f := faces_ih.mp e_in_fs,
    cases exists_f with f' f'_conds,
    cases f'_conds with f'_in_fs e_in_f',
    split,
      show list ℕ, from f',
      split,
        apply or.inr f'_in_fs,
      assumption,
  intro h,
  cases h with f' f'_conds,
  apply (edge_in_added_face f (faces_set_from_lst fs) e).mpr,
  cases f'_conds with f'_conds e_in_f',
  cases f'_conds with f_eq_f' f'_in_fs,
    rw f_eq_f' at e_in_f',
    apply or.inl,
    assumption,
  apply or.inr,
  apply faces_ih.mpr,
  split,
    show list ℕ, from f',
  split; assumption,
end
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
theorem σα_maps_neighbours {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ x y z, σα_maps K.σ x y z = tt → in_neighbours_opt G y x :=
begin 
  intros x y z map_cond,
  simp [σα_maps] at map_cond,
  cases h : K.σ.val_at y with c,
    rw h at map_cond,
    simp [σα_maps._match_1] at map_cond,
    apply false.elim,
    assumption,
  rw h at map_cond,
  simp [σα_maps._match_1] at map_cond,
  cases h' : c.next.val_at x,
    rw h' at map_cond,
    simp [σα_maps._match_2] at map_cond,
    apply false.elim,
    assumption,
  rw ←σ_edges_consistent K,
  rw h,
  simp [cycle_contains_key_opt],
  apply key_in_map_iff_evals,
  exact h',
end
theorem edge_in_list_of_σα_cons {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ xs x', is_list_of_σα K.σ (xs ++ [x']) → ∀ x y, edge_in_list (x, y) xs → in_neighbours_opt G y x :=
begin
  intros xs x',
  induction xs with x₁ xs,
    simp [is_list_of_σα],
  intro list_cond,
  intros x y,
  intro xy_in_list,
  cases xs with x₂ xs,
    simp [edge_in_list] at xy_in_list,
    apply false.elim,
    assumption,
  cases xs with x₃ xs,
    simp [edge_in_list] at xy_in_list,
    cases xy_in_list with x_eq_x₁ y_eq_x₂,
    simp [is_list_of_σα] at list_cond,
    apply σα_maps_neighbours K x y x',
    rw [x_eq_x₁, y_eq_x₂], assumption,
  by_cases h : (x, y) = (x₁, x₂),
    injection h with x_eq_x₁ y_eq_x₂,
    rw [x_eq_x₁, y_eq_x₂] at xy_in_list,
    simp [is_list_of_σα] at list_cond,
    apply σα_maps_neighbours K x y x₃,
    rw [x_eq_x₁, y_eq_x₂],
    apply list_cond.left,
  simp [edge_in_list] at xy_in_list,
  cases xy_in_list,
    have xy_eq_x₁x₂ : (x, y) = (x₁, x₂),
      rw [xy_in_list.left, xy_in_list.right],
    apply false.elim (h xy_eq_x₁x₂),
    have xy_in_list' : edge_in_list (x, y) (x₂ :: x₃ :: xs),
      simp [xy_in_list, edge_in_list],
    simp [is_list_of_σα] at list_cond,
    apply xs_ih,
      apply list_cond.right,
    assumption,
end
lemma edge_not_end_to_edge_in_shorter_list (x y x' y' : ℕ) (xs : list ℕ) :
  edge_in_list (x, y) (xs ++ [x', y']) → (x, y) ≠ (x', y') → edge_in_list (x, y) (xs ++ [x']) :=
begin
  induction xs with z' xs,
    simp [edge_in_list],
    intros x_eq_x' y_eq_y' h,
    apply (h x_eq_x') y_eq_y',
  simp [edge_in_list],
  intros xy_in x_neq_y,
  cases xs with w' xs,
    simp [edge_in_list] at xy_in,
    simp [edge_in_list],
    cases xy_in,
      apply xy_in,
    cases xy_in with x_eq_x' y_eq_y',
    apply false.elim ((x_neq_y x_eq_x') y_eq_y'),
  by_cases (x, y) = (z', w'),
    simp [edge_in_list],
    apply or.inl,
    injection h with x_eq_z' y_eq_w',
    rw [x_eq_z', y_eq_w'], simp,
  apply or.inr,
  apply xs_ih,
  simp [edge_in_list] at xy_in,
  cases xy_in,
    cases xy_in with x_eq_z' y_eq_w',
    rw [x_eq_z', y_eq_w'] at h,
    simp at h,
    apply false.elim h,
  apply xy_in,
  simp, assumption,
end
lemma edge_in_face_in_extended_list (x y x' y' : ℕ) (xs : list ℕ) : 
  edge_in_face (x, y) (x' :: y' :: xs) → edge_in_list (x, y) (x' :: y' :: xs ++ [x']) :=
begin
  cases xs with z' xs,
    simp [edge_in_face, edge_in_list],
    intro h,
    repeat {cases h, simp [*]},
  simp [edge_in_face, edge_in_list],
  intro h,
  by_cases h' : (x, y) = (x', y'),
    injection h' with x_eq_x' y_eq_y',
    apply or.inl, split; assumption,
  cases h,
    apply or.inl, assumption,
  cases h,
    apply or.inr, apply or.inl, assumption,
  apply or.inr, apply or.inr,
  rw list.cons_append_assoc,
  apply edge_not_end_to_edge_in_shorter_list,
  apply h,
  apply h',
end
theorem edge_in_face_of_σα_cons {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ xs, is_face_of_σα K.σ xs → ∀ x y, edge_in_face (x, y) xs → in_neighbours_opt G y x :=
begin
  intro xs,
  cases xs with x' xs,
    simp [is_face_of_σα, edge_in_face],
  cases xs with y' xs,
    simp [is_face_of_σα, edge_in_face],
  intros h x y h',
  apply edge_in_list_of_σα_cons K (x' :: y' :: xs ++ [x']) y', 
  simp [is_face_of_σα] at h,
  simp, assumption,
  apply edge_in_face_in_extended_list,
  assumption,
end
theorem all_face_edges_in_neighbours {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ x y, (∃ f, f ∈ K.faces ∧ edge_in_face (x, y) f) → in_neighbours_opt G y x :=
begin
  intros x y,
  have comp_fs_consistent := K.composition_faces_consistent,
  intro h,
  cases h with f f_conds,
  cases f_conds with f_in_faces xy_in_f,
  have f_is_face_of := comp_fs_consistent f f_in_faces,
  apply edge_in_face_of_σα_cons K f f_is_face_of,
  apply xy_in_f,
end
def edges_set (G : simple_irreflexive_graph) : tset (lex ℕ ℕ) := sorry
theorem in_edges_set_iff (G : simple_irreflexive_graph) : 
  ∀ x y, (y, x) ∈ (edges_set G) ↔ in_neighbours_opt G x y := sorry
theorem edges_set_size (G : simple_irreflexive_graph) :
  (edges_set G).size = 2 * (G.edge_size) := sorry
theorem pair_in_face_iff_edge {G : simple_irreflexive_graph} (K : combinatorial_map G) :
  ∀ x y, (∃ f, f ∈ K.faces ∧ edge_in_face (x, y) f) ↔ in_neighbours_opt G y x :=
begin
  intros x y,
  split,
    apply all_face_edges_in_neighbours,
  rw ←in_faces_set_iff,
  rw ←in_edges_set_iff G y x,
  apply tset_inclusion_size_eq_to_tset_eq,
  rw edges_set_size,
  apply K.num_of_edges,
  intros e e_in_faces_set,
  have h := (in_faces_set_iff K.faces e).mp e_in_faces_set,
  cases e with x' y',
  rw in_edges_set_iff,
  apply all_face_edges_in_neighbours,
  apply h,
end
theorem add_unique_list_preserves {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (l : list ℕ) :
  add_list_to_set_if_unique acc l = some t → ∀ e, acc.elem e → t.elem e :=
begin
  intros add_l_to_set e e_in_acc,
  induction l with x xs generalizing acc,
    simp [add_list_to_set_if_unique] at add_l_to_set,
    rw ←add_l_to_set,
    assumption,
  cases xs with y xs,
    simp [add_list_to_set_if_unique] at add_l_to_set,
    rw ←add_l_to_set,
    assumption,
  simp [add_list_to_set_if_unique] at add_l_to_set,
  cases acc.elem (x, y),
    simp [add_list_to_set_if_unique._match_1] at add_l_to_set,
    apply l_ih (acc.add (x, y)) add_l_to_set,
      apply tset.add_preserves, assumption,
  simp [add_list_to_set_if_unique._match_1] at add_l_to_set,
  apply false.elim, assumption,
end
theorem add_unique_list_to_set {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (l : list ℕ) :
  add_list_to_set_if_unique acc l = some t → ∀ e, edge_in_list e l → t.elem e :=
begin
  intros add_l_to_set e e_in_l, 
  induction l with x xs generalizing acc,
    simp [edge_in_list] at e_in_l,
    apply false.elim, assumption,
  cases xs with y xs,
    simp [edge_in_list] at e_in_l,
    apply false.elim, assumption,
  simp [edge_in_list] at e_in_l,
  simp [add_list_to_set_if_unique] at add_l_to_set,
  cases acc.elem (x,y),
    simp [add_list_to_set_if_unique._match_1] at add_l_to_set,
    cases e_in_l with e_eq_xy,
      apply add_unique_list_preserves (acc.add (x, y)) (y :: xs),
      assumption,
      apply tset.elem_add, assumption,
    apply l_ih e_in_l (acc.add (x,y)) add_l_to_set,
  simp [add_list_to_set_if_unique._match_1] at add_l_to_set,
  apply false.elim, assumption,
end
theorem add_unique_list_lst_not_in_acc {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (l : list ℕ) :
  add_list_to_set_if_unique acc l = some t → ∀ e, edge_in_list e l → ¬ (acc.elem e) :=
begin 
  intros add_l e e_in_l e_in_t,
  induction l with x xs generalizing acc,
    simp [edge_in_list] at e_in_l, assumption,
  cases xs with y xs,
    simp [edge_in_list] at e_in_l, assumption,
  simp [add_list_to_set_if_unique] at add_l,
  simp [edge_in_list] at e_in_l,
  cases e_in_l with e_eq_xy,
    rw e_eq_xy at e_in_t,
    have xy_in_t := (to_bool_iff _).mpr e_in_t,
    simp at xy_in_t,
    rw xy_in_t at add_l,
    simp [add_list_to_set_if_unique] at add_l,
    assumption,
  cases acc.elem (x, y),
    simp [add_list_to_set_if_unique] at add_l,
    apply l_ih e_in_l (acc.add (x, y)) add_l,
      apply tset.add_preserves, assumption,
  simp [add_list_to_set_if_unique] at add_l,
  assumption,
end
theorem add_unique_face_fc_not_in_acc {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (l : list ℕ) :
  add_face_to_set_if_unique acc l = some t → ∀ e, edge_in_face e l → ¬ (acc.elem e) :=
begin
  cases l with x xs,
    simp [add_face_to_set_if_unique, edge_in_face],
  cases xs with y xs,
    simp [edge_in_face],
  unfold edge_in_face, unfold add_face_to_set_if_unique,
  intros add_l e e_in,
  apply add_unique_list_lst_not_in_acc acc (x :: y :: xs ++ [x, y]) add_l,
  simp,
  simp at e_in,
  assumption,
end
theorem add_unique_face_preserves {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (f : list ℕ) : 
  add_face_to_set_if_unique acc f = some t → ∀ e, acc.elem e → t.elem e :=
begin 
  cases f with x xs,
    simp [add_face_to_set_if_unique],
    intro acc_eq_t,
    rw acc_eq_t,
    simp,
  cases xs with y xs,
    simp [add_face_to_set_if_unique],
    intro acc_eq_t,
    rw acc_eq_t,
    simp,
  simp [add_face_to_set_if_unique],
  apply add_unique_list_preserves,
end
theorem add_unique_face_to_set {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) (f : list ℕ) :
  add_face_to_set_if_unique acc f = some t → ∀ e, edge_in_face e f → t.elem e :=
begin
  cases f with x xs,
    simp [add_face_to_set_if_unique, edge_in_face],
  cases xs with y xs,
    simp [edge_in_face],
  simp [add_face_to_set_if_unique, edge_in_face],
  apply add_unique_list_to_set,
end
theorem faces_unique_edges_aux_edge_not_in_later {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) 
  (f : list ℕ) (fs : list (list ℕ)) : faces_unique_edges_aux acc (f :: fs) = some t → 
    ∀ e, edge_in_face e f ∨ acc.elem e → ∀ g, g ∈ fs → ¬ (edge_in_face e g) :=
begin
  intros unique_cond e e_in g g_in_fs e_in_g, 
  simp [faces_unique_edges_aux] at unique_cond,
  cases h : add_face_to_set_if_unique acc f with t',
    rw h at unique_cond,
    simp [faces_unique_edges_aux] at unique_cond,
    assumption,
  rw h at unique_cond,
  simp [faces_unique_edges_aux] at unique_cond,
  induction fs with f' fs generalizing acc f t',
    simp at g_in_fs, assumption,
  simp at g_in_fs,
  cases h' : add_face_to_set_if_unique t' f' with t'',
    simp [faces_unique_edges_aux] at unique_cond,
    rw h' at unique_cond,
    simp [faces_unique_edges_aux] at unique_cond,
    assumption,
  simp [faces_unique_edges_aux] at unique_cond,
  rw h' at unique_cond,
  simp [faces_unique_edges_aux] at unique_cond,
  cases g_in_fs with g_eq_f',
    cases e_in with e_in_f e_in_acc,
      have e_in_t' := add_unique_face_to_set acc f h e e_in_f,
      rw g_eq_f' at e_in_g,
      apply add_unique_face_fc_not_in_acc t' f' h' e e_in_g e_in_t',
    have e_in_t' := add_unique_face_preserves acc f h e e_in_acc,
    rw g_eq_f' at e_in_g,
    apply add_unique_face_fc_not_in_acc t' f' h' e e_in_g e_in_t',
  cases e_in with e_in_f e_in_acc,
    have e_in_t' := add_unique_face_to_set acc f h e e_in_f,
    apply fs_ih g_in_fs t' f' t'' (or.inr e_in_t') h' unique_cond,
  have e_in_t' := add_unique_face_preserves acc f h e e_in_acc,
  apply fs_ih g_in_fs t' f' t'' (or.inr e_in_t') h' unique_cond,
end
theorem faces_unique_edges_aux_diff_faces  {t : tset (lex ℕ ℕ)} (acc : tset (lex ℕ ℕ)) 
  (faces : list (list ℕ)) : faces_unique_edges_aux acc faces = some t →
  ∀ i j : fin (faces.length), 
    ∀ e, edge_in_face e (list.nth_le faces i.val i.property) →
          edge_in_face e (list.nth_le faces j.val j.property) →
    i = j :=
begin
  intros unique_cond i j e e_in_fi e_in_fj,
  induction faces with f fs generalizing i j acc,
    cases i with i i_prop,
    simp at i_prop,
    apply false.elim, assumption,
  simp [faces_unique_edges_aux] at unique_cond,
  cases i with i i_prop,
  cases j with j j_prop,
  cases i,
    simp [list.nth_le] at e_in_fi,
    cases j,
      simp,
    simp [list.nth_le] at e_in_fj,
    cases h : add_face_to_set_if_unique acc f with t',
      rw h at unique_cond,
      simp [faces_unique_edges_aux] at unique_cond,
      apply false.elim, assumption,
    rw h at unique_cond,
    simp [faces_unique_edges_aux] at unique_cond,

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
