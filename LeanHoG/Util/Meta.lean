import Lean

namespace LeanHoG

open Lean

/-- Whether `declName` already holds a declaration of type `expectedType`. -/
def hasReusableDecl (declName : Name) (expectedType : Expr) : Meta.MetaM Bool := do
  let some info := (← getEnv).find? declName | return false
  -- The comparison runs at a new metavariable depth so that a mismatch cannot leave
  -- `expectedType`'s metavariables assigned behind it.
  if ← Meta.withNewMCtxDepth (Meta.isDefEq info.type (← instantiateMVars expectedType)) then
    return true
  else
    throwError "the name {declName} is already taken by a declaration of type\
      {indentExpr info.type}\nbut this graph needs one of type{indentExpr expectedType}"

end LeanHoG
