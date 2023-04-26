import Qq
import Graph

set_option autoImplicit false

namespace HoG

open Qq

def edgeOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(Edge $n) := do
  let arr ← j.getArr?
  have a : Q(Nat) := Lean.mkRawNatLit (← arr[0]!.getNat?)
  have b : Q(Nat) := Lean.mkRawNatLit (← arr[1]!.getNat?)
  have H1 : Q(Nat.blt $a $n = true) := (q(Eq.refl true) : Lean.Expr)
  have H2 : Q(Nat.blt $b $a = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Edge.mk' $n $a $b $H1 $H2)

partial def treeOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(STree (Edge $n)) := do
  let arr ← j.getArr? 
  match arr with
  | #[e, l, r] => pure q(STree.node $(← edgeOfJson n e) $(← treeOfJson n l) $(← treeOfJson n r))
  | #[] => pure q(STree.empty)
  | #[v] => pure q(STree.leaf $(← edgeOfJson n v))
  | _ => throw "invalid tree format"

partial def graphOfJson (j : Lean.Json) : Except String Q(Graph) := do
    let njson ← j.getObjVal? "vertexSize"
    have n : Q(Nat) := Lean.mkRawNatLit (← njson.getNat?)
    let edges : Q(STree (Edge $n)) ← (treeOfJson n (← j.getObjVal? "edges"))
    pure q(Graph.mk $n $edges) -- here it dies with: reduceEval: failed to evaluate argument __do_lift✝¹

-- The Lean name generated from a string
def hogName (hogId : String) : Lean.Name := (.str (.str .anonymous "HoG") hogId)

-- loading a hog as a function
-- def loadHog (hogId : String) : IO Unit  := do
--   let packageDir ← Mathlib.getPackageDir "HoG"
--   let dataDir := ((packageDir.join "..").join "..").join "pigpen" -- folder with the JSON files
--   let fileName := (dataDir.join hogId).withExtension "json"
--   let file ← IO.FS.readFile fileName
--   let graph : Except String (Q(Graph)) := do
--     let json ← Lean.Json.parse file 
--     graphOfJson json
--   let .ok value := graph | throw (IO.userError "could not load the JSON file")
--   whatToDoHere <| Lean.addAndCompile <| .defnDecl {
--     name := hogName hogId
--     levelParams := []
--     type := q(Graph)
--     value
--     hints := .regular 0
--     safety := .safe
--   }

elab "loadHog" hogId:str : command => do
  let packageDir ← Mathlib.getPackageDir "HoG"
  let dataDir := ((packageDir.join "..").join "..").join "pigpen" -- folder with the JSON files
  let fileName := (dataDir.join hogId.getString).withExtension "json"
  let file ← IO.FS.readFile fileName
  let graph : Except String (Q(Graph)) := do
    let json ← Lean.Json.parse file 
    graphOfJson json
  let .ok value := graph | throwError "could not load the JSON file"
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := hogName hogId.getString
    levelParams := []
    type := q(Graph)
    value
    hints := .regular 0
    safety := .safe
  }

-- elab "getHog" hogId:str : term => do
--   let hog := hogName hogId.getString
--   let env ← Lean.getEnv
--   match env.contains hog with
--   | true => pure (Lean.mkConst hog [])
--   | false => loadHog hogId ; pure (Lean.mkConst hog [])

end HoG