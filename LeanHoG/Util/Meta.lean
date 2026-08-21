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
    Meta.addInstance declName .global 1000
    return mkConst declName
  return cert

/-- Assert `type` as an axiom named `graphName.suffix`, and return the conclusion `derive`
draws from it — that is, `derive`'s result with the axiom substituted for its hypothesis.

**`derive` runs before the axiom is committed, and the order matters.** Deriving the
conclusion is the expensive part, so if it ran after `addDecl` then exhausting the heartbeats
there would leave the axiom in the environment on a command that reports failure: the user
sees an error and still has the hole. So `derive` is handed a local hypothesis of `type`
instead, and the axiom is only added once it has succeeded.

An axiom of exactly this type already under the name is reused rather than re-declared, which
is what makes a second run on the same graph work; `hasReusableDecl` is what confirms it says
literally what is needed. Otherwise the name is global under `register`, and beneath the
enclosing declaration without it — a tactic may not add a name outside its own prefix. -/
def withUnsatAxiom (graphName : Name) (suffix : String) (register : Bool) (type : Expr)
    (derive : Expr → Elab.TermElabM Expr) : Elab.TermElabM Expr := do
  let globalName : Name := .str graphName suffix
  let declName : Name ←
    if (← hasReusableDecl globalName type) ∨ register then
      pure globalName
    else
      match ← Elab.Term.getDeclName? with
      | some enclosing => pure (enclosing ++ globalName)
      | none => pure globalName
  let derivation ← Meta.withLocalDeclD `hCnfUnsat type fun h => do
    Meta.mkLambdaFVars #[h] (← instantiateMVars (← derive h))
  unless ← hasReusableDecl declName type do
    let decl := Declaration.axiomDecl {
      name        := declName,
      levelParams := [],
      type        := type,
      isUnsafe    := false
    }
    trace[Elab.axiom] "{declName} : {type}"
    Elab.Term.ensureNoUnassignedMVars decl
    -- Past this point nothing but `addDecl` itself can fail.
    addDecl decl
    logWarning m!"added axiom {declName} : {type}"
  return .app derivation (mkConst declName)

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
