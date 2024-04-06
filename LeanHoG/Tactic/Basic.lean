import Lean
import LeanHoG.Graph
import LeanHoG.Tactic.SearchDSL
import LeanHoG.Tactic.Options
import LeanHoG.Invariant.HamiltonianPath.Basic
import Qq

import Aesop.Util.Basic
import Std.Data.List.Basic

namespace LeanHoG

open Lean Widget Elab Command Term Meta Qq Tactic Qq

/-- Evaluate an expression into a Nat -/
unsafe def evaluateNat (e : Expr) : MetaM Nat := do
  let n ← evalExpr' Nat ``Nat e
  return n

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
    let n ← evaluateNat n
    return .comp .plus (.integralInv inv) (.nat n)

  | ~q(fun G => HAdd.hAdd ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .comp .plus (.integralInv inv) (.nat n)

  | ~q(fun G => HSub.hSub ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .comp .minus (.integralInv inv) (.nat n)

  | ~q(fun G => HDiv.hDiv ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .comp .div (.integralInv inv) (.nat n)

  | ~q(fun G => HMul.hMul ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .comp .times (.integralInv inv) (.nat n)

  | ~q(fun G => $f G) =>
    let inv ← decomposeIntegralInvQ f
    return (.integralInv inv)
  | _ => throwError s!"cannot decompose formula, got {e}"

unsafe def decomposeComparisonQ {G : Q(Sort)} (e : Q($G → Prop)) : MetaM HoGEnquiry := do
  match e with
  | ~q(fun G => @LT.lt Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .IntegralEnquiry { inv := inv, op := .Lt, val := n }
  | ~q(fun G => Nat.lt ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .IntegralEnquiry { inv := inv, op := .Lt, val := n }
  | ~q(fun G => @LE.le Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .IntegralEnquiry { inv := inv, op := .Le, val := n }
  | ~q(fun G => Nat.le ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .IntegralEnquiry { inv := inv, op := .Le, val := n }
  | ~q(fun G => @GT.gt Nat _ ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
    return .IntegralEnquiry { inv := inv, op := .Gt, val := n }
  | ~q(fun G => @Eq Nat ($f G) $n) =>
    let inv ← decomposeIntegralInvQ f
    let n ← evaluateNat n
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

end LeanHoG
