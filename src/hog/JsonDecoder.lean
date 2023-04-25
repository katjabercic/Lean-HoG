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

elab "getHog" hogId:str : command => do
  let packageDir ← Mathlib.getPackageDir "HoG"
  let dataDir := ((packageDir.join "..").join "..").join "pigpen" -- folder with the JSON files
  let fileName := (dataDir.join hogId.getString).withExtension "json"
  let file ← IO.FS.readFile fileName
  let graph : Except String (Q(Graph)) := do
    let json ← Lean.Json.parse file 
    graphOfJson json
  let .ok value := graph | throwError "could not load the JSON file"
  Lean.Elab.Command.liftCoreM <| Lean.addDecl <| .defnDecl {
    name := (.str (.str .anonymous "HoG") hogId.getString)
    levelParams := []
    type := q(Graph)
    value
    hints := .regular 0
    safety := .safe
  }
  
-- getHog "hog00000"

end HoG