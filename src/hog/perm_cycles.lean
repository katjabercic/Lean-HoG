import .python group_theory.perm.cycles .tactic
open equiv expr

meta def eval_match_fun_aux : expr → tactic string 
| (expr.app e@(app (app (app _ (app _ x)) _) (app (app _ (app _ n_e)) y)) rest) := 
  do
    n ← tactic.eval_expr ℕ n_e,
    x' ← tactic.eval_expr ℕ x,
    y' ← tactic.eval_expr (fin n) y,
    evs ← eval_match_fun_aux rest,
    return $ (to_string x') ++ " " ++ (format.to_string y') ++ "\n" ++ evs 
| (app (app _ (app _ n)) x) :=
  do
    n' ← tactic.eval_expr ℕ n,
    x' ← tactic.eval_expr (fin n') x, 
    pure $ "_ " ++ to_string x'
| e := tactic.fail $ "unknown expression " ++ to_string e 

-- Evaluate a function of the form `ite (ite (...))`
meta def eval_match_fun (e : expr) : tactic (expr × string) :=
do
  e' ← tactic.whnf e,
  (match e' with
  | (expr.lam nm _ (app _ m) (app (const n _) _)) := 
    do
      m' ← tactic.eval_expr ℕ m,
      f ← tactic.get_decl n,
      (match f with
      | (declaration.defn _ _ _ (expr.lam _ _ _ bod) _ _) := (
        do
          s ← eval_match_fun_aux bod,
          return (m, s)
        )
      | _ := tactic.fail "wrong format 2"
      end)
  | _ := tactic.fail "wrong format"
  end)

def f  (i : fin 3) : (fin 3) :=
(match i.val with
| 0 := 1
| 1 := 0
| 2 := 2 
| _ := 0
end : (fin 3))

def parse_int : parser ℕ :=
do
  n ← parser.nat,
  parser.ch ' ' <|> parser.eps,
  return n

def parse_cycle : parser (list ℕ) :=
do
  ns ← parser.many1 parse_int,
  parser.ch '\n',
  return ns

def parse_cycles : parser (list (list ℕ)) :=
  do
    parser.many1 parse_cycle

def cycle_list_to_fun {n : ℕ} (cycle : list (fin n)) (x : fin n) : 
fin n :=
if (x ∈ cycle) then (
  let i := ((list.index_of x cycle) + 1) % n in
  (match (list.nth cycle i) with 
  | none := x 
  | some y := y
  end))
else x

def cycle_list_to_inv_fun {n : ℕ} (cycle : list (fin n)) (x : fin n) : 
fin n :=
if (x ∈ cycle) then (
  let i := ((list.index_of x cycle) - 1) % n in
  (match (list.nth cycle i) with 
  | none := x 
  | some y := y
  end))
else x

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

meta def list_to_fun {n : ℕ} (l : list (fin n)) : tactic expr :=
(match l with
| [] := tactic.fail "empty list"
| ls@(x::xs) := (
let start := x in
do
  pe ← list_to_fun_aux start ls,
  let pe' := ```(λ _x_1 : fin %%n, %%pe),
  tactic.i_to_expr pe'
)
end)

meta def nat_to_fin (n : expr) : tactic expr :=
let p := ``(fact (0 < %%n)) in 
let q := ``(0 < %%n) in
do
  e ← tactic.i_to_expr p,
  v ← tactic.i_to_expr q,
  (_, s) ← tactic.solve_aux v bool_reflect,
  (_, t) ← tactic.solve_aux e (tactic.exact `((@fact_iff %%v).mpr %%s)),
  return t

meta def nat_list_to_fin (n : ℕ) (l : list ℕ) : tactic (list (fin n)) :=
let n' := `(n) in
do
  n_gt_0 ← nat_to_fin n',
  ls ← list.mmap 
    (λ x : ℕ, 
    let x' := `(x) in
    let e := `(@fin.of_nat' %%n' %%n_gt_0 %%x') in 
    do
      v ← tactic.eval_expr (fin n) e,
      return v
  ) l,
  return ls

meta def build_perms_expr {n : ℕ} (cycles : list (list (fin n))) : tactic (list expr) := --(equiv.perm (fin n)) :=--(list (equiv.perm (fin n))) :=
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

meta def list_to_expr : list expr → tactic (option pexpr) 
| [] := do return none
| (x :: xs) :=
  do
    rest ← list_to_expr xs,
    (match rest with
    | none := 
      do
        x' ← return x,
        let pl := ``(list.cons %%x list.nil),
        return (some pl)
    | (some es) :=
      do
        e ← return es,
        x' ← return x,
        let pl := ``(list.cons %%x' %%e),
        return (some pl)

  end)

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
-- TODO add missing conditions
let pe : pexpr := 
  ```((list.prod %%ls).to_fun = %%f') in
do
  prop_e ← tactic.i_to_expr pe,
  (_, prop) ← tactic.solve_aux prop_e bool_reflect,
  return (ls, prop)

def cycles_of {n : ℕ} (f : fin n → fin n) := {g : list (perm (fin n)) // (list.prod g).to_fun = f}

meta def cycle_factors (f : expr) : tactic expr :=
do
  (n, i) ← eval_match_fun f,
  n' ← tactic.eval_expr ℕ n,
  let input := i,
  let cmd := "src/hog/scripts/cycle_factors.py",
  output ← python.run cmd $ string.to_char_buffer input,
  let parsed_cycles := parser.run parse_cycles output,
  let cycles := (match parsed_cycles with
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

structure cyclic_decomposition :=
  {n : ℕ}
  (f : fin n → fin n)
  (cycles : cycles_of f . gen_factorization)
