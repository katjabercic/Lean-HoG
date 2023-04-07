import Lean
import TreeSet

structure GraphInfo : Type :=
  (vertexSize : Nat)
  (edgeSize : Nat)
  (minDegree : Option Nat)
  (maxDegree : Option Nat)
  (isRegular : Bool)
  (isBipartite : Bool)
deriving Repr

def findGraphSuchThat (p : GraphInfo → Bool) : 
  List GraphInfo → Option GraphInfo
  | [] => none
  | g :: gs => if p g then g else findGraphSuchThat p gs

open Lean in
def list_graphInvariants := (Expr.app (Expr.const ``List [levelZero]) (Expr.const ``GraphInfo []))

open Lean Lean.Elab.Tactic Expr Meta in 
elab "try_add_invariants_to_ctx" : tactic =>
  withMainContext do
      let m1 ← Meta.mkFreshExprMVar list_graphInvariants (userName := `graph_invariants)
      m1.mvarId!.withContext do
        let s ← saveState
        try
          if ← isDefEq (mkMVar m1.mvarId!) (Expr.const `Hog.invariants []) then
            liftMetaTactic fun mvarId => do
              let t ← m1.mvarId!.getType
              let mvarIdNew ← mvarId.define `graph_invariants t (Expr.const `Hog.invariants [])
              let (_, mvarIdNew) ← mvarIdNew.intro1P
              return [mvarIdNew]
          else
            logError m!"Unable to find Hog.invariants, please add 'import Data.Invariants' at the beginning of the file"
            restoreState s
        catch _ =>
          logError m!"Unable to find Hog.invariants, please add 'import Data.Invariants' at the beginning of the file"
          restoreState s

open Lean Lean.Elab.Tactic Expr Meta in 
elab "try_find_invariant " p:term : tactic =>
  withMainContext do
    let ctx ← MonadLCtx.getLCtx
    let my_list ← LocalContext.findFromUserName? ctx `graph_invariants
    let p ← elabTerm p none
    let my_fun := Expr.const `findGraphSuchThat [] 
    liftMetaTactic fun mvarId => do
      let my_app ← mkAppM ``findGraphSuchThat #[p, my_list.toExpr]
      let reduced ← reduce my_app
      logInfo m!"Found invariant: {reduced}"
      return [mvarId]