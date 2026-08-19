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

/-- A Lean name for a certificate: `certName` beneath the graph's own name. -/
def certificateName (graphName : Name) (certName : String) : Name :=
  (.str graphName certName)

/-- The term to use as a certificate of type `certType`: the declaration `declName` if it
already holds one for this graph, a fresh declaration under that name if `register` is set,
and otherwise `cert` itself.

The `#check_*` commands want a declaration, since registering a reusable certificate — one
visible to instance synthesis, and to `#show_hamiltonian_path` — is the point of the command.

The tactics must not ask for one. Lean elaborates declarations in parallel and lets each add
only names beneath its own prefix, so a named theorem cannot introduce `G.TwoColoringI` and
fails with `cannot add declaration ... as it is restricted to the prefix ...`. With
`register := false` the certificate goes into the proof term directly, which costs nothing:
every `…OfData` builder returns a self-contained term. -/
def certificateTerm (declName : Name) (certType cert : Expr) (register : Bool) :
    Elab.TermElabM Expr := do
  if ← hasReusableDecl declName certType then
    return mkConst declName
  if register then
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := certType
      value := cert
      hints := .regular 0
      safety := .safe
    }
    Meta.addInstance declName .global 42
    return mkConst declName
  return cert

/-- Assemble `∀ (v : G.vertex), P v` from one proof per vertex, given in index order, as a
chain of `Fin.cases` bottoming out at `Fin.elim0`.

Built as syntax and elaborated against `expected` rather than assembled as an `Expr`: each
`Fin.cases` in the chain needs a motive phrased in terms of the next `Fin.succ`, and letting
the elaborator infer those from the expected type is considerably less work than computing
them. -/
def mkForallVertexProof (expected : Expr) (proofs : Array Expr) : Elab.TermElabM Expr := do
  let mut stx ← `(fun i => Fin.elim0 i)
  for e in proofs.reverse do
    let eStx ← Elab.Term.exprToSyntax e
    stx ← `(Fin.cases $eStx $stx)
  let proof ← Elab.Term.elabTerm stx (some expected)
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

end LeanHoG
