import system.io
import data.fin
open expr tactic
open interactive (parse)
open interactive.types (texpr)

namespace python
/-
Command with input and output.
-/
meta def buffered_cmd (args : io.process.spawn_args) 
  (input : char_buffer) : io char_buffer :=
do
  child ← io.proc.spawn 
    { args with 
      stdout := io.process.stdio.piped, 
      stdin := io.process.stdio.piped
    },
  io.fs.write child.stdin input,
  io.fs.close child.stdin,
  buf ← io.fs.read_to_end child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process failed with status" ++ to_string exitv,
  return buf 
/-
Runs the specified python script
`arg`: script name,
`input`: the input that will be sent to the script
-/
meta def run (arg : string) (input : char_buffer) : tactic char_buffer :=
let cmd' := "python3",
    s_args := {io.process.spawn_args. cmd := cmd', args := [arg]} in
do
  c ← tactic.unsafe_run_io $ io.env.get_cwd,
  tactic.unsafe_run_io $ buffered_cmd s_args input

/-
Helper functions for parsing output from python programs
-/
def parse_int : parser ℕ :=
do
  n ← parser.nat,
  parser.ch ' ' <|> parser.eps,
  return n

/-
Helper functions to convert lean data into a form
that can be exported to python
-/

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
| e := tactic.fail $ 
  "expression does not match expected form " ++ 
  to_string e 

/- 
Evaluate a function `f` of the form `λ x, f._match_1 x` into a
string whose every line contains the pair `x f(x)`.
The last line represents the catch all value.
-/
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
      | _ := tactic.fail "expression does not contain the expected _match_1 call"
      end)
  | _ := tactic.fail "expression does not represent a match function"
  end)

end python

namespace expr
/-
General functions for working with expressions
-/
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
end expr