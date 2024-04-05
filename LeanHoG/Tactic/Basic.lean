import Lean
import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Invariant.Hamiltonicity.Basic
import Qq

import Aesop.Util.Basic
import Std.Data.List.Basic

namespace LeanHoG

open Lean Widget Elab Command Term Meta Qq Tactic Qq

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

instance : ToString (Invariant × ComparisonOp × Nat) where
  toString := fun (i, op, n) =>
    s!"{i} {op} {n}"

def decomposeIntegralInvQ (e : Q(Graph → Nat)) : MetaM IntegralInvariant := do
  match e with
  | ~q(fun G => Graph.vertexSize G) => return IntegralInvariant.NumberOfVertices
  | ~q(fun G => Graph.edgeSize G) => return IntegralInvariant.NumberOfEdges
  | ~q(fun G => Graph.minimumDegree G) => return IntegralInvariant.MinimumDegree
  | _ => throwError s!"cannot decompose integral invariant, got {e}"

def decomposeBoolInvQ (e : Q(Graph → Prop)) : MetaM BoolInvariant := do
  match e with
  | ~q(fun G => Graph.isHamiltonian G) => return BoolInvariant.Hamiltonian
  | ~q(fun G => Graph.isTraceable G) => return BoolInvariant.Traceable
  | _ => throwError s!"cannot decompose Boolean invariant, got {e}"

unsafe def decomposeFormulaQ (e : Q(Graph → Nat)) : MetaM ArithExpr := do
  match e with
  | ~q(fun G => Nat.add ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .comp .plus (.integralInv inv) (.nat n)

  | ~q(fun G => HAdd.hAdd ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .comp .plus (.integralInv inv) (.nat n)

  | ~q(fun G => HSub.hSub ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .comp .minus (.integralInv inv) (.nat n)

  | ~q(fun G => HDiv.hDiv ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .comp .div (.integralInv inv) (.nat n)

  | ~q(fun G => HMul.hMul ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .comp .times (.integralInv inv) (.nat n)

  | ~q(fun G => $f G) =>
    let inv ← decomposeIntegralInvQ f
    return (.integralInv inv)
  | _ => throwError s!"cannot decompose formula, got {e}"

unsafe def decomposeComparisonQ {G : Q(Sort)} (e : Q($G → Prop)) : MetaM HoGEnquiry := do
  match e with
  | ~q(fun G => @LT.lt Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Lt, val := n }
  | ~q(fun G => Nat.lt ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Lt, val := n }
  | ~q(fun G => @LE.le Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Le, val := n }
  | ~q(fun G => Nat.le ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Le, val := n }
  | ~q(fun G => @GT.gt Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Gt, val := n }
  | ~q(fun G => @Eq Nat ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← decomposeNat n
    return .IntegralEnquiry { inv := inv, op := .Eq, val := n }

  | ~q(fun G => @LT.lt Nat _ ($f G) ($g G)) =>
    let lhs ← decomposeFormulaQ f
    let rhs ← decomposeFormulaQ g
    return .FormulaEnquiry { lhs := lhs, rhs := rhs, cmp := .Lt }
  | ~q(fun G => @Eq Nat ($f G) ($g G)) =>
    let lhs ← decomposeFormulaQ f
    let rhs ← decomposeFormulaQ g
    return .FormulaEnquiry { lhs := lhs, rhs := rhs, cmp := .Eq }
  | ~q(fun G => $f G) =>
    let inv ← decomposeBoolInvQ f
    return .BoolEnquiry { inv := inv, val := true }
  | _ => throwError m!"cannot decompose comparison, got {e}"

def decomposeAndQ {G : Q(Sort)} (e : Q($G → Prop)) : MetaM (Q(Prop) × Q(Prop)) := do
  match e with
  | ~q(fun G => $P G ∧ $Q G) => return (P,Q)
  | _ => throwError m!"cannot decompose conjunction, got: {e}"

partial def decomposeAndsQ {G : Q(Sort)} (e : Q($G → Prop)) : MetaM (List Q($G → Prop)) := do
  match e with
  | ~q(fun G => $P G ∧ $Q G) =>
    let lhs ← decomposeAndsQ P
    let rhs ← decomposeAndsQ Q
    return lhs ++ rhs
  | ~q(fun G => $P G) => return [P]
  | _ => throwError m!"cannot decompose conjunction, got: {e}"

unsafe def decomposeExistsQ (e : Q(Prop)) : MetaM (List HoGEnquiry) := do
  match e with
  | ~q(∃ G, $P G) =>
    let Ps ← decomposeAndsQ P
    let enquiries ← List.mapM (fun R => do
       let Q ← decomposeComparisonQ R
       return Q
    ) Ps
    return enquiries
  | _ => throwError "cannot decompose exists, got: {e}"

syntax (name := searchForExampleInHoG) "search_for_example" : tactic

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
        let enqs ← decomposeExistsQ goalType
        let hash := hash enqs
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
              evalDecide stx
              Lean.logInfo s!"Closed goal using {graphId.getId}"
              -- Visualize the graph we used to close the goal
              -- TODO: Make this an option
              let wi : Expr ←
                elabWidgetInstanceSpecAux (mkIdent `visualize) (← ``((Graph.toVisualizationFormat $graphId)))
              let wi : WidgetInstance ← evalWidgetInstance wi
              savePanelWidgetInfo wi.javascriptHash wi.props stx
            else
              continue
        else
          throwError "Could not find any graphs matching criteria"

      catch e =>
        throwError m!"search failed: {e.toMessageData}"

  | _ => throwUnsupportedSyntax

set_option leanHoG.pythonExecutable "/home/jure/source-control/Lean/Lean-HoG/.venv/bin/python"

syntax (name := foo) "foo" : tactic

@[tactic foo]
unsafe def fooImpl : Tactic
  | stx@`(tactic|foo) =>
    withMainContext do
      let goal ← getMainGoal
      let goalDecl ← goal.getDecl
      let goalType := goalDecl.type
      let _ ← decomposeExistsQ goalType
  | _ => throwUnsupportedSyntax

-- example : ∃ (G : Graph), G.isTraceable ∧ G.vertexSize > 3 ∧ (G.minimumDegree < G.vertexSize / 2) := by
--   search_for_example

end LeanHoG
