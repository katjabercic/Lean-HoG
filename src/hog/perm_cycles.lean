import .python group_theory.perm.cycles .tactic
open equiv expr
/-
Generate the proof of `fact (0 < n)`
-/
meta def n_gt_0 (n : expr) : tactic expr :=
let p := ``(fact (0 < %%n)) in 
let q := ``(0 < %%n) in
do
  e ← tactic.i_to_expr p,
  v ← tactic.i_to_expr q,
  (_, s) ← tactic.solve_aux v bool_reflect,
  (_, t) ← tactic.solve_aux e (tactic.exact `((@fact_iff %%v).mpr %%s)),
  return t
/-
Given `n : ℕ` and a list `l : list ℕ`, generate `list (fin n)` where the
i-th element of the new list is `l[i] % n : fin n`
-/
meta def nat_list_to_fin (n : ℕ) (l : list ℕ) : tactic (list (fin n)) :=
let n' := `(n) in
do
  n_gt_0_prop ← n_gt_0 n',
  ls ← list.mmap 
    (λ x : ℕ, 
    let x' := `(x) in
    let e := `(@fin.of_nat' %%n' %%n_gt_0_prop %%x') in 
    do
      v ← tactic.eval_expr (fin n) e,
      return v
  ) l,
  return ls

meta def list_to_fun_aux {n : ℕ} (start : fin n) : 
list (fin n) → tactic pexpr
| [] := (
  let m : ℕ := ↑start in
  return ```(m : fin %%n)
)
| (x :: []) :=
let x' : ℕ := ↑x in
let m : ℕ := ↑start in
do   
  return ```(ite (_x_1 = %%x') (%%m : fin %%n) _x_1)
| (x :: y :: xs) :=
let x' : ℕ := ↑x in
let y' : ℕ := ↑y in
do
  pe ← list_to_fun_aux (y :: xs),
  return ```(ite (_x_1 = %%x') (%%y' : fin %%n) %%pe)

-- Convert a list representing a cycle into a function
meta def list_to_fun {n : ℕ} (l : list (fin n)) : tactic expr :=
(match l with
| [] := tactic.fail "the cycle is empty"
| ls@(x::xs) := (
let start := x in
do
  pe ← list_to_fun_aux start ls,
  let pe' := ```(λ _x_1 : fin %%n, %%pe),
  tactic.i_to_expr pe'
)
end)

-- convert a list of lists representing cycles to a cycle 
meta def build_perms_expr {n : ℕ} (cycles : list (list (fin n))) : 
tactic (list expr) := 
list.mmap 
(
  λ cycle : list (fin n),
  do
    f ← list_to_fun cycle,
    f_inv ← list_to_fun (list.reverse cycle),
    let l_inv_pe : pexpr := ``(function.left_inverse %%f_inv %%f),
    let r_inv_pe : pexpr := ``(function.right_inverse %%f_inv %%f),
    l_inv_e ← tactic.i_to_expr l_inv_pe,
    r_inv_e ← tactic.i_to_expr r_inv_pe,
    (_, l_inv_proof_e) ← tactic.solve_aux l_inv_e bool_reflect,
    (_, r_inv_proof_e) ← tactic.solve_aux r_inv_e bool_reflect,
    let perm_pexpr : pexpr := ```(
      {equiv. to_fun:=%%f, 
      inv_fun:=%%f_inv,
      left_inv:=%%l_inv_proof_e,
      right_inv:=%%r_inv_proof_e}),
    e ← tactic.i_to_expr perm_pexpr,
    return e
) cycles

def cycle_factors_prop {n : ℕ} (f : fin n → fin n) (g : list (perm (fin n))) :=  
  -- the permutations represent the expected function
  (list.prod g).to_fun = f ∧ 
  -- the permutations are actually cycles
  (list.all g 
    (λ h : equiv.perm (fin n), 
      ∃ x : fin n, h x ≠ x ∧ 
        (∀ y : fin n, h y ≠ y →
          ∃ j : fin n, ((h.to_fun^[j])) x = y)
    )
  ) ∧
  -- the cycles are disjoint
  (list.pairwise
    (λ f g : equiv.perm (fin n), 
          ∀ x : fin n, 
            (f.to_fun x ≠ x → g.to_fun x = x) ∧ 
            (g.to_fun x ≠ x → f.to_fun x = x)
    )
    g
  )
def cycles_of {n : ℕ} (f : fin n → fin n) := 
  {g : list (perm (fin n)) // cycle_factors_prop f g}

/-
Generates the proof that the permutations in `l` actually give
a cycle factorization of `f`
-/
meta def cycles_give_f (n : expr) (f : expr) (l : list expr) :
tactic (expr × expr) :=
do
  l_pe ← list_to_expr l,
  f' ← tactic.whnf f,
  l_e ← (match l_pe with
  | none := do tactic.fail "empty list"
  | (some e) := return e
  end),
  ls ← tactic.i_to_expr l_e,
  let pe : pexpr :=
  ```((list.prod %%ls).to_fun = %%f' ∧
      (list.all %%ls 
        (λ f : equiv.perm (fin %%n), 
          ∃ x : fin %%n, f.to_fun x ≠ x ∧ 
          (∀ y : fin %%n, f.to_fun y ≠ y → 
            (∃ j : fin %%n, (f.to_fun^[j]) x = y)
          )
        )
      ) ∧
      (list.pairwise 
        (λ f g : equiv.perm (fin %%n), 
          ∀ x : fin %%n, 
            (f.to_fun x ≠ x → g.to_fun x = x) ∧ 
            (g.to_fun x ≠ x → f.to_fun x = x)
        )
        %%ls
      ) 
  ),
  prop_e ← tactic.i_to_expr pe,
  (_, prop) ← tactic.solve_aux prop_e bool_reflect,
  return (ls, prop)

/-
Helper functions for parsing cycles from external output
-/
def parse_cycle : parser (list ℕ) :=
do
  ns ← parser.many1 python.parse_int,
  parser.ch '\n',
  return ns

def parse_cycles : parser (list (list ℕ)) :=
  do
    parser.many1 parse_cycle

/-
Tactics for generating the cyclic factorizatin of the function `f`
-/
meta def cycle_factors (f : expr) : tactic expr :=
do
  (n, i) ← python.eval_match_fun f,
  n' ← tactic.eval_expr ℕ n,
  let input := i,
  let cmd := "src/hog/scripts/cycle_factors.py",
  output ← python.run cmd $ string.to_char_buffer input,
  let parsed_cycles := parser.run parse_cycles output,
  let cycles := 
  (match parsed_cycles with
  | sum.inl _ := []
  | sum.inr cs := cs
  end), 
  ls ← list.mmap (λ l, nat_list_to_fin n' l) cycles,
  perms_e ← build_perms_expr ls,
  (perms, cs_give_f) ← @cycles_give_f n f perms_e,
  return `(⟨%%perms, %%cs_give_f⟩ : @cycles_of %%n %%f)

meta def gen_factorization : tactic unit :=
do
  t ← tactic.target,
  `(cycles_of %%f) ← tactic.target,
  e ← cycle_factors f,
  tactic.exact e

namespace tactic
namespace interactive

setup_tactic_parser
meta def cycle_factors  (e : parse texpr) : tactic expr :=
do
  e' ← i_to_expr e,
  _root_.cycle_factors e'

end interactive
end tactic
/-
structure cyclic_decomposition :=
  {n : ℕ}
  (f : fin n → fin n)
  (cycles : cycles_of f . gen_factorization)
-/