import .tree_set

namespace map_path
open tree_set
/- Some functions and lemmas that need to be defined for tmap -/
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
def tmap.val_at_safe {α β : Type} [linear_order α] {next : tmap α β} (key : α) :
  next.contains_key key → β := sorry
theorem tmap.val_at_safe_cond {α β : Type} [linear_order α] {next : tmap α β} (key : α) 
  (k_in_next : next.contains_key key) : some (tmap.val_at_safe key k_in_next) = next.val_at key := sorry
set_option trace.check true
theorem tmap_size_1_implies_all_els_eq {α β : Type} [linear_order α] : Π {next : tmap α β}, 
  next.size = 1 → ∀ (x y : α), next.contains_key x → next.contains_key y → x = y :=
sorry
/- End of functions and lemmas that need to be defined for tmap -/
-- Iterate the tmap next n times from some starting parameter
def tmap_iter {α : Type} [linear_order α] (next : tmap α α) : α → ℕ → option α
| x 0 := some x
| x (n + 1) := 
  (match next.val_at x with
  | none := none
  | some a := tmap_iter a n
  end)

-- tmap_iter with n + 1 can be rewriten as the "composition" of two tmap_iter uses
def tmap_iter_suc {α : Type} [linear_order α] (next : tmap α α) {n : ℕ} {src dst : α} 
  (h : tmap_iter next src n = some dst) : tmap_iter next src (n + 1) = tmap_iter next dst 1 :=
begin
  induction n generalizing src,
    -- case 0
    simp [tmap_iter],
    simp [tmap_iter] at h,
  -- case n + 1
  rewrite h,
  simp [tmap_iter] at h,
  simp [tmap_iter],
  cases (next.val_at src),
  simp [tmap_iter._match_1] at h,
  apply false.elim h,
  simp [tmap_iter._match_1],
  simp [tmap_iter._match_1] at h,
  have h' := n_ih h,
  simp [tmap_iter] at h',
  apply h',
end
/-
  The function that walks from src to dst in n steps. 
  Returns tt if such a walk can be done while checking that
  it doesn't reach dst before the last step.
-/
def walk (dst : ℕ) (next : tmap ℕ ℕ) : ℕ → ℕ → bool
| src 0 := dst = src
| src (n + 1) := 
  src ≠ dst ∧
  (match next.val_at src with
  | none := ff
  | some val := walk val n 
  end : bool)

-- dst is next after src if the map evaluates src to dst
def map_next_is (next : tmap ℕ ℕ) (src dst : ℕ) : Prop :=
  next.val_at src = some dst

/-
  A map_path can either consist of a single element (source) or 
  it can be an extension of an existing map_path.
-/
inductive map_path (next : tmap ℕ ℕ) : ℕ → ℕ → Type
| source (src : ℕ)  :  map_path src src
| extend {src dst dst' : ℕ} (p : map_path src dst) (can_extend : map_next_is next dst dst') : map_path src dst'

-- checks that x can be found in a given path
def in_path (next : tmap ℕ ℕ) (x : ℕ) : 
  Π {src dst : ℕ}, map_path next src dst → Prop
| _ _ (map_path.source src) := src = x
| src dst' (map_path.extend p can_extend) := dst' = x ∨ in_path p

-- The last element in a map_path doesn't appear earlier
def end_unique {next : tmap ℕ ℕ} : Π {src dst : ℕ}, map_path next src dst → Prop 
| _ _ (map_path.source src) := true -- source obviously has a unique end
| src dst' (map_path.extend p can_extend) := ¬ (in_path next dst' p) -- end unique if it doesn't appear in the front

-- Merges a map_path from src to dst and a map_path from src' to dst' to a path from src to dst'
def map_path_append {next : tmap ℕ ℕ} : Π {src dst src' dst'}, 
  map_path next src dst → map_path next src' dst' → map_next_is next dst src' → 
  map_path next src dst'
| src dst .(src') .(_) p (map_path.source src') can_extend := map_path.extend p can_extend
| src dst src' dst' p (map_path.extend p' can_extend') can_extend := 
  let p'' := map_path_append p p' can_extend in -- inductively define the path without dst'
  map_path.extend p'' can_extend' -- extend to dst'

def map_path.size {next : tmap ℕ ℕ} : Π {src dst : ℕ}, Π (p : map_path next src dst), ℕ
| src dst (map_path.source .(src)) := 0 -- size starts at 0 to simplify induction on the size
| src dst (map_path.extend p' can_extend) := p'.size + 1

/-
  For an element x, that is in the map_path, it converts the path from src to dst 
  to a path from src to x
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
  @eq.rec_on _ _ (λ y, map_path next src y) _ src_eq_x p
| src dst x p@(map_path.extend p' can_extend) x_in_p := 
  decidable.cases_on (eq.decidable dst x) 
  (λ dst_neq_x, -- if dst ≠ x 
    let x_in_p' : in_path next x p' := -- since x is in p and dst ≠ x, x is in p'
      begin
        simp [in_path] at x_in_p,
        cases x_in_p with dst_eq_x x_in_p',
          apply false.elim (dst_neq_x dst_eq_x),
        apply x_in_p',
      end
    in src_to_elem p' x_in_p')
  (λ dst_eq_x, @eq.rec_on _ _ (λ y, map_path next src y) _ dst_eq_x p)
/-
  For an element x, that is in the map_path, it converts the path from src to dst 
  to a path from x to dst 
-/
def elem_to_dst {next : tmap ℕ ℕ} : Π {src dst x : ℕ}, Π (p : map_path next src dst),
  Π (x_in_p : in_path next x p), map_path next x dst 
| src dst x p@(map_path.source .(src)) x_in_p := (
    let src_eq_x : src = x := 
      begin
        simp [in_path] at x_in_p,
        assumption,
      end
    in
    @eq.rec_on _ _ (λ y, map_path next y src) _ src_eq_x p
  )
| src dst x p@(map_path.extend p' can_extend) x_in_p := (
    decidable.cases_on (eq.decidable dst x)
    (λ dst_neq_x, 
      let x_in_p' : in_path next x p' := -- since x is in p and dst ≠ x, x is in p'
        begin
          simp [in_path] at x_in_p,
          cases x_in_p with dst_eq_x x_in_p',
            apply false.elim (dst_neq_x dst_eq_x),
          apply x_in_p',
        end
      in
      let elem_to_dst' := elem_to_dst p' x_in_p' in -- inductively define path from x to dst'
      map_path.extend elem_to_dst' can_extend -- extend the previous path to a path from x to dst
    )
    (λ dst_eq_x, -- If x is the dst then we simply return a path which consists of 1 element (size 0) 
      let p'' : map_path next dst dst := map_path.source dst in 
      @eq.rec_on _ _ (λ y, map_path next y dst) _ dst_eq_x p''
    )
  )
/-
  A map_path from src to dst of size n means that if we iterate tmap.val_at n times,
  starting from src, we reach dst.
-/
theorem map_path_iter_src_dst {next : tmap ℕ ℕ} {src dst : ℕ} : Π (p : map_path next src dst), 
  tmap_iter next src (p.size) = some dst :=
begin
  intro p,
  induction p,
    -- p = source
    simp [tmap_iter, map_path.size],
  -- p = extend
  have h := tmap_iter_suc next p_ih,
  simp [map_path.size],
  rw h,
  simp [tmap_iter],
  unfold map_next_is at p_can_extend,
  rw p_can_extend,
  simp [tmap_iter._match_1],
end
/-
  If element is not in map_path then the destination is not equal to said element
-/
def elem_not_in_path_to_dst_neq_elem {next : tmap ℕ ℕ} {src dst val : ℕ} (p : map_path next src dst)
  (elem_nin_path : ¬ (in_path next val p)) : dst ≠ val :=
begin
  intro dst_eq_val,
  cases p,
    simp [in_path] at elem_nin_path,
    apply false.elim (elem_nin_path dst_eq_val),
    simp [in_path] at elem_nin_path,
    apply false.elim (elem_nin_path (or.inl dst_eq_val)),
end

--  Extend map path from the start
def extend_map_path {next : tmap ℕ ℕ} : Π {src dst src' : ℕ}, 
   Π (p : map_path next src dst), Π (can_extend : map_next_is next src' src), 
  map_path next src' dst 
| src dst src' p@(map_path.source _) can_extend := 
  map_path.extend (map_path.source src') can_extend
| src dst src' (map_path.extend path can_extend') can_extend := 
  map_path.extend (extend_map_path path can_extend) can_extend'

-- Extending a map_path from the start increases the size by 1
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
/- 
  If we extend a map_path from the left an element is in the map if it's in eleement we are adding
  or if it is in the rest of the map
-/
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
/-
  If we extend a map_path with a unique end from the front and the new element 
  is different from the destination of the map_path, then the new
  map_path also has a unique end
-/
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
  If we have a walk of length greater than 0, then the element that comes
  after source is not none
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
/-
  The element we get from walk_src_next is in fact the element that follows the source
-/
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
-- Convert a walk from src to dst to a map_path from src to dst
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
-- The walk_to_path function gives us a path of length n (where n is the length of the walk)
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
-- The path we get from walk_to_path has a unique end
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
-- next.val_at of some element of a map_path that isn't last is in the map_path
def next_of_extended_in_path {next : tmap ℕ ℕ} : Π {x src dst dst' : ℕ}, 
  Π (p : map_path next src dst), Π (can_extend : map_next_is next dst dst'), 
  in_path next x p → ∃ y : ℕ, next.val_at x = some y ∧ in_path next y (map_path.extend p can_extend) :=
begin
  intros x src dst dst' p can_extend in_p,
  induction p generalizing dst',
    simp [in_path] at in_p,
    split,
      show ℕ, from dst',
    split,
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
-- If we remove the last element from a map_path with a unique end the end is still unique
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
/-
  Convert a map_path in some tmap to a map_path in a map with one element remove.
  Assumes the element that is removed doesn't appear in the map path
-/
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
      exact elem_not_in_path_to_dst_neq_elem p' x_nin_p',
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

-- map_path_smaller_map preserves size
theorem map_path_smaller_map_size {next : tmap ℕ ℕ} {x src dst : ℕ}
  (p : map_path next src dst) (h : next.contains_key x) (x_nin_p : ¬ (in_path next x p)) :
  p.size = (map_path_smaller_map p h x_nin_p).size :=
begin
  induction p,
    simp [map_path.size, map_path_smaller_map],
  simp [map_path.size, map_path_smaller_map],
  apply p_ih,
end
-- map_path_smaller_map preserves all elements
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
-- map_path_smaller preserves end_unique
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
/-
  If the length of a map_path is equal to the length of the map plus 1 then all 
  elements from the map appear in the map_path
-/
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
    have p'_elem_cond := map_path_smaller_elem p_p dst_in_map p_end_unique,
    have p_dst_in_next := key_in_map_iff_evals p_dst dst p_can_extend, 
    have dst_neq_p_dst := elem_not_in_path_to_dst_neq_elem p_p p_end_unique,
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
        (map_path_smaller_map_end_unique p_p p_p_end_unique dst_in_map p_end_unique)
        (remove_preserves_other_keys dst next dst_in_map p_dst p_dst_in_next p_dst_neq_dst)
        new_map_size 
        x 
        x_in_new_map,
    apply (p'_elem_cond x).mpr,
    apply x_in_p',
end
end map_path
