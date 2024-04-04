import Lean
import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Invariant.Hamiltonicity.Basic

import Aesop.Util.Basic
import Std.Data.List.Basic

namespace LeanHoG

open Lean Widget Elab Command Term Meta Qq Tactic

/-- Express the expression `e` as an exists statement over the type given by `name`.
    If it is of this form return the arguments, otherwise return `none`.
-/
def asExistsOver (e : Expr) (type : Name) : MetaM Expr := do
  if Expr.isAppOf e ``Exists then
    let args := Expr.getAppArgs e
    let xTy := args[0]!
    let body := args[1]!
    let p ←  Meta.isDefEq xTy (Expr.const type [])
    if p == true then
      let (_, _, conclusion) ← Meta.lambdaMetaTelescope body
      return conclusion
    else throwError "exists not over expected type {type}"
  else
    throwError "not of the form ∃ x, t"

/-- Decompose `e` as an application `f args` and return `args` -/
def decomposeAppOf (e : Expr) (f : Name) (normalizeFirst := false) : MetaM (Array Expr) := do
  let e := if normalizeFirst then ← whnf e else e
  if Expr.isAppOf e f then
    let args := Expr.getAppArgs e
    return args
  else
    throwError s!"expr not app of {f}"

def decomposeAnd (e : Expr) : MetaM (Expr × Expr) := do
  let args ← decomposeAppOf e ``And
  if h : args.size = 2 then
    return (args[0]'(by rw [h]; norm_num), args[1]'(by rw [h]; norm_num))
  else
    throwError "expr not a conjunction"

partial def decomposeAnds (e : Expr) : MetaM (List Expr) := do
  try
    let (e₁, e₂) ← decomposeAnd e
    let es₁ ← decomposeAnds e₁
    let es₂ ← decomposeAnds e₂
    return es₁ ++ es₂
  catch _ =>
    return [e]

def decomposeNatLe (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let args ← decomposeAppOf e ``Nat.le
    match args with
    | #[e₁, e₂] => return some (e₁, e₂)
    | _ => return none
  catch _ => return none

def decomposeNatLt (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let args ← decomposeAppOf e ``Nat.lt
    match args with
    | #[e₁, e₂] => return some (e₁, e₂)
    | _ => return none
  catch _ => return none

def decomposeLt (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  try
    let args ← decomposeAppOf e ``LT.lt
    match args with
    | #[type, _, e₁, e₂] => return some (type, e₁, e₂)
    | _ => return none
  catch _ => return none

def decomposeLe (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  try
    let args ← decomposeAppOf e ``LE.le
    match args with
    | #[type, _, e₁, e₂] => return some (type, e₁, e₂)
    | _ => return none
  catch _ => return none


def decomposeEq (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  try
    let args ← decomposeAppOf e ``Eq
    match args with
    | #[type, e₁, e₂] => return some (type, e₁, e₂)
    | _ => return none
  catch _ => return none

unsafe def decomposeNat (e : Expr) : MetaM Nat := do
  let n ← evalExpr' Nat ``Nat e
  return n

unsafe def decomposeBool (e : Expr) : MetaM Bool := do
  let b ← evalExpr' Bool ``Bool e
  return b

def isNatSucc (e : Expr) : MetaM Bool := do
  try
    let _ ← decomposeAppOf e ``Nat.succ (normalizeFirst := false)
    return true
  catch _ =>
    return false

/-- Returns (type, comparison, lhs rhs) of a comparison. -/
def decomposeComp (e : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  match (← decomposeNatLe e),
        (← decomposeNatLt e),
        (← decomposeLt e),
        (← decomposeLe e),
        (← decomposeEq e) with
  | some (lhs, rhs), none, none, none, none => return (mkConst ``Nat, mkConst ``Nat.le, lhs, rhs)
  | none, some (lhs, rhs), none, none, none => return (mkConst ``Nat, mkConst ``Nat.le, lhs, rhs)
  | none, none, some (t, lhs, rhs), none, none => return (t, mkConst ``LT.lt, lhs, rhs)
  | none, none, none, some (t, lhs, rhs), none => return (t, mkConst ``LE.le, lhs, rhs)
  | none, none, none, none, some (t, lhs, rhs) => return (t, mkConst ``Eq, lhs, rhs)
  | _,_,_,_,_ => throwError "expr {e} not a comparison"

def asBoolInvariant (e : Expr) : MetaM BoolInvariant := do
  match e with
  | .const f _  =>
    match f with
    | ``Graph.isTraceable => return .Traceable
    | ``Graph.isHamiltonian => return .Hamiltonian
    | n => throwError s!"not known invariant: {n}"
  | _ => throwError "expr {e} not an invariant"

def asInvariant (e : Expr) : MetaM Invariant := do
  match e with
  | .const f _  =>
    match f with
    -- | ``Graph.isTraceable => return (.BoolInvariant .Traceable)
    -- | ``Graph.isHamiltonian => return (.BoolInvariant .Hamiltonian)
    | ``Graph.vertexSize =>  return (.IntegralInvariant .NumberOfVertices)
    | ``Graph.edgeSize => return (.IntegralInvariant .NumberOfEdges)
    | n => throwError s!"not known invariant: {n}"
  | _ => throwError "expr {e} not an invariant"

/-- Missing NEGATION case -/
def decomposeProp (e : Expr) : MetaM (BoolInvariant × Bool) := do
  match e with
  | .app f args =>
    -- Have to check if application of negation
    try
      let _ ← decomposeAppOf e ``Not
      let (inv, _) ← decomposeProp args
      return (inv, false)
    catch _ =>
      let inv ← asBoolInvariant f
      return (inv, true)
  | _ =>
    throwError s!"unknown prop {e}"

def decomposeInvariantApp (e : Expr) : MetaM (Option (Invariant × Expr)) := do
  match e with
  | .app f args =>
    try
      let inv ← asInvariant f
      return some (inv, args)
    catch _ => return none
  | _ => return none

def asComparisonOp (e : Expr) : MetaM ComparisonOp := do
  match e with
  | .const f _  =>
    match f with
    | ``Eq => return .Eq
    | ``Nat.lt => return .Lt
    | ``Nat.le => return .Le
    | ``LE.le => return .Le
    | ``LT.lt => return .Lt
    | _ => throwError s!"expr {e} not a comparison"
  | _ => throwError s!"expr {e} not a comparison"

unsafe def decomposeComparison (type op lhs rhs : Expr) :
  dbg_trace s!"{lhs}, {rhs}"
  MetaM HoGEnquiry := do
  if ← (isDefEq type (mkConst ``Nat)) then
    match (← decomposeInvariantApp lhs), (← decomposeInvariantApp rhs) with
    | some (.IntegralInvariant ii, _args), none =>
      let n ← decomposeNat rhs
      let op ← asComparisonOp op
      return .IntegralEnquiry { inv := ii, op := op, val := n }
    | none, some (.IntegralInvariant ii, _args) =>
      let n ← decomposeNat rhs
      let op ← asComparisonOp op
      return .IntegralEnquiry { inv := ii, op := op, val := n }
    | _, _ => throwError "comparison not of expected form"
  else if ← (isDefEq type (mkSort levelZero)) then
    match (← decomposeInvariantApp lhs), (← decomposeInvariantApp rhs) with
    | some (.BoolInvariant bi, _), none =>
      let b ← decomposeBool rhs
      let _op ← asComparisonOp op -- TODO: Check the comparison is equality
      return .BoolEnquiry { inv := bi, val := b }
    | none, some (.BoolInvariant bi, _) =>
      let b ← decomposeBool rhs
      let _op ← asComparisonOp op -- TODO: Check the comparison is equality
      return .BoolEnquiry { inv := bi, val := b }
    | _, _ => throwError "comparison not of expected form"
  else
    throwError "comparison not of expected form"

unsafe def decompose (e : Expr) : MetaM (List HoGEnquiry) := do
  let body ← asExistsOver e ``Graph
  let args ← decomposeAnds body
  let comparisons ← args.mapM (fun (arg : Expr) => do
    try
      let (t,op,lhs,rhs) ← decomposeComp arg
      let enq ← decomposeComparison t op lhs rhs
      return enq
    catch _ =>
      let (inv, val) ← decomposeProp arg
      return .BoolEnquiry { inv := inv, val := val }
  )
  return comparisons

def buildEnquiry (e : Expr) : MetaM (Option HoGEnquiry) := do
  sorry

def buildQuery (e : Expr) : MetaM (Option (List HoGEnquiry)) := do
  sorry

syntax (name := searchForExampleInHoG) "search_for_example" : tactic

instance : ToString (Invariant × ComparisonOp × Nat) where
  toString := fun (i, op, n) =>
    s!"{i} {op} {n}"

#check Declaration

@[tactic searchForExampleInHoG]
unsafe def searchForExampleInHoGImpl : Tactic
  | stx@`(tactic|search_for_example) =>
    withMainContext do
      let goal ← getMainGoal
      let goalDecl ← goal.getDecl
      let goalType := goalDecl.type
      let graphType : Expr ← mkConst ``Graph
      let exists_intro ← mkConst ``Exists.intro
      try
        let enqs ← decompose goalType
        let hash := hash enqs
        -- IO.println s!"{hash}"
        let query := HoGQuery.build enqs
        let graphs ← liftCommandElabM (queryDatabaseForExamples [query] hash)
        if h : graphs.length > 0 then
          let ⟨graphId⟩ := graphs[0]'(by simp_all only [not_lt_zero'])
          -- IO.println f!"Found such a graph: {name}"
          let mvarIds' ← Lean.MVarId.apply goal exists_intro
          replaceMainGoal mvarIds'
          let newGoals ← getGoals
          for goal in newGoals do
            -- find the goal with type Graph and try to close it with `graph`
            let goalDecl ← goal.getDecl
            let goalType := goalDecl.type
            if ← Meta.isDefEq goalType graphType then
              -- check that the goal is not already assigned
              goal.checkNotAssigned `search_for_counterexample
              -- try to close the goal with the found graph
              goal.withContext do
                let r ← Lean.Elab.Tactic.elabTermEnsuringType graphId goalType
                goal.assign r
              -- Now try to simp which will among other things look for instance for e.g. HamiltonianPath
              evalSimp stx
              Lean.logInfo s!"Closed goal using {graphId.getId}"
            else
              continue
        else
          throwError "Could not find any graphs matching criteria"

      catch e =>
        throwError m!"search failed: {e.toMessageData}"

  | _ => throwUnsupportedSyntax

-- #search_hog hog{ numberOfVertices < 5 ∧ traceable = true }

set_option leanHoG.pythonExecutable "/home/jure/source-control/Lean/Lean-HoG/.venv/bin/python"

def a : Nat := 2

elab "use_a" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    closeMainGoalUsing (checkUnassigned := false) fun type => do
      let a_name := mkIdent ``a
      let r ← Lean.Elab.Tactic.elabTermEnsuringType a_name type
      return r

example : Nat := by
  exact a

example : ∃ (G : Graph), G.vertexSize = 7 ∧ G.isTraceable := by
  search_for_example

end LeanHoG
