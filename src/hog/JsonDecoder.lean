import Qq
import Graph
import EdgeSize

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
    let json_v ← j.getObjVal? "vertexSize"
    have v : Q(Nat) := Lean.mkRawNatLit (← json_v.getNat?)
    let edges : Q(STree (Edge $v)) ← (treeOfJson v (← j.getObjVal? "edges"))
    pure q(Graph.mk $v $edges)

def edgeSizeOfJson (G : Q(Graph)) (j : Lean.Json) : Except String Q(EdgeSize $G) := do
  let j ← j.getObjVal? "edgeSize"
  have e : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  have H : Q(Nat.beq ($G).edgeTree.size $e = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(EdgeSize.mk' $G $e $H)

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

-- lifting from exception monad to the Elab.Command monad
def liftExcept {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok res => pure res
  | .error msg => throwError msg

elab "loadHog" hogId:str : command => do
  let packageDir ← Mathlib.getPackageDir "HoG"
  let dataDir := ((packageDir.join "..").join "..").join "pigpen" -- folder with the JSON files
  let fileName := (dataDir.join hogId.getString).withExtension "json"
  let file ← IO.FS.readFile fileName
  let json ← liftExcept <| Lean.Json.parse file
  let graphQ : Q(Graph) ← liftExcept <| graphOfJson json
  -- load the graph
  let graphName := hogName hogId.getString
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := graphName
    levelParams := []
    type := q(Graph)
    value := graphQ
    hints := .regular 0
    safety := .safe
  }
  have graph : Q(Graph) := Lean.mkConst graphName []
  -- load the edgeSize instance
  let edgeSizeQ : Q(EdgeSize $graph) ← liftExcept <| edgeSizeOfJson graph json
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := hogName (hogId.getString ++ "_edgeSize")
    levelParams := []
    type := q(EdgeSize $graph)
    value := edgeSizeQ
    hints := .regular 0
    safety := .safe
  }
  -- how do declare the instance?

loadHog "hog00000"
-- #check hog00000.edgeSize_is

-- elab "getHog" hogId:str : term => do
--   let hog := hogName hogId.getString
--   let env ← Lean.getEnv
--   match env.contains hog with
--   | true => pure (Lean.mkConst hog [])
--   | false => loadHog hogId ; pure (Lean.mkConst hog [])

end HoG
