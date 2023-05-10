import Qq
import Graph
import EdgeSize
import ConnectedComponents
import TreeMap

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

def natOfJson (j : Lean.Json) : Except String Q(Nat) := do
  have n : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  pure n

def finOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(Fin $n) := do
  have k : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  have H : Q(Nat.blt $k $n = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(Fin.mk $k (Nat.le_of_ble_eq_true $H))

def vertexOfJson (G : Q(Graph)) (j : Lean.Json) : Except String Q(Graph.vertex $G) := do
  finOfJson (q(Graph.vertexSize $G)) j

partial def treeOfJson (n : Q(Nat)) (j : Lean.Json) : Except String Q(STree (Edge $n)) := do
  let arr ← j.getArr?
  match arr with
  | #[] => pure q(STree.empty)
  | #[v] => pure q(STree.leaf $(← edgeOfJson n v))
  | #[e, l, r] => pure q(STree.node $(← edgeOfJson n e) $(← treeOfJson n l) $(← treeOfJson n r))
  | _ => throw "invalid tree format"

partial def mapTreeOfJson (α β : Q(Type))
  (keyOfJson : Lean.Json → Except String Q($α))
  (valOfJson : Lean.Json → Except String Q($β))
  (j : Lean.Json) : Except String Q(Map $α $β) := do
  let arr ← j.getArr?
  match arr with
  | #[] => pure q(Map.empty)
  | #[k, v] => pure q(Map.leaf $(← keyOfJson k) $(← valOfJson v))
  | #[k, v, l, r] => pure q(Map.node $(← keyOfJson k) $(← valOfJson v) $(← mapTreeOfJson α β keyOfJson valOfJson l) $(← mapTreeOfJson α β keyOfJson valOfJson r))
  | _ => throw "invalid tree map format"

partial def mapOfJson (α β : Q(Type))
  (keyOfJson : Lean.Json → Except String Q($α))
  (valOfJson : Lean.Json → Except String Q($β))
  (j : Lean.Json) : Except String Q($α → $β) := do
  let arr ← j.getArr?
  match arr with
  | #[] => _ -- empty domain
  | #[treeJ, defaultJ] =>
    let tree ← mapTreeOfJson α β keyOfJson valOfJson treeJ
    let defaultValue ← valOfJson defaultJ
    pure q(Map.getD $tree $defaultValue) 
  | _ => throw "invalid map format"


partial def graphOfJson (j : Lean.Json) : Except String Q(Graph) := do
    let json_v ← j.getObjVal? "vertexSize"
    have v : Q(Nat) := Lean.mkRawNatLit (← json_v.getNat?)
    let edges : Q(STree (Edge $v)) ← (treeOfJson v (← j.getObjVal? "edges"))
    pure q(Graph.mk $v $edges)

def edgeSizeOfJson (G : Q(Graph)) (j : Lean.Json) : Except String Q(EdgeSize $G) := do
  have e : Q(Nat) := Lean.mkRawNatLit (← j.getNat?)
  have H : Q(Nat.beq ($G).edgeTree.size $e = true) := (q(Eq.refl true) : Lean.Expr)
  pure q(EdgeSize.mk' $G $e $H)

def componentsCertificateOfJson (G : Q(Graph)) (j : Lean.Json) : Except String Q(ComponentsCertificate $G) := do
  let valJ ← j.getObjVal? "val"
  have val : Q(Nat) := Lean.mkRawNatLit (← valJ.getNat?)
  let componentJ ← j.getObjVal? "component"
  let componentMap ← mapOfJson q(Graph.vertex $G) q(Fin $val) (vertexOfJson G) (finOfJson val) componentJ
  let rootJ ← j.getObjVal? "root"
  let rootMap ← mapOfJson q(Graph.vertex $G) q(Graph.vertex $G) (vertexOfJson G) (vertexOfJson G) rootJ
  let nextJ ← j.getObjVal? "next"
  let nextMap ← mapOfJson q(Graph.vertex $G) q(Graph.vertex $G) (vertexOfJson G) (vertexOfJson G) nextJ
  let distToRootJ ← j.getObjVal? "distToRoot"
  let distToRootMap ← mapOfJson q(Graph.vertex $G) q(Graph.vertex $G) (vertexOfJson G) natOfJson distToRootJ
  sorry -- we need a smart constructor here

-- The Lean name generated from a string
def hogName (hogId : String) : Lean.Name := (.str (.str .anonymous "HoG") hogId)

-- A name for an instance of a particular HoG
def hogInstanceName (hogId : String) (inst : String) : Lean.Name :=
  (.str (hogName hogId) inst)

-- lifting from exception monad to the Elab.Command monad
def liftExcept {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok res => pure res
  | .error msg => throwError msg

elab "#loadHog" hogId:str : command => do
  let packageDir ← Mathlib.getPackageDir "HoG"
  let dataDir := ((packageDir.join "..").join "..").join "pigpen" -- folder with the JSON files
  let fileName := (dataDir.join hogId.getString).withExtension "json"
  let file ← IO.FS.readFile fileName
  let json ← liftExcept <| Lean.Json.parse file
  let graphJ ← liftExcept <| json.getObjVal? "graph"
  let graphQ : Q(Graph) ← liftExcept <| graphOfJson graphJ
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
  let edgeSizeName := hogInstanceName hogId.getString "edgeSizeI"
  let edgeSizeJ ← liftExcept <| json.getObjVal? "edgeSize"
  let edgeSizeQ : Q(EdgeSize $graph) ← liftExcept <| edgeSizeOfJson graph edgeSizeJ
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := edgeSizeName
    levelParams := []
    type := q(EdgeSize $graph)
    value := edgeSizeQ
    hints := .regular 0
    safety := .safe
  }
  Lean.Elab.Command.liftTermElabM <| Lean.Meta.addInstance edgeSizeName .scoped 42
  -- load the components certificate
  let componentsCertificateName := hogInstanceName hogId.getString "componentsCertificateI"
  let componentsCertificateJ ← liftExcept <| json.getObjVal? "componentsCertificate"
  let componentsCertificateQ : Q(ComponentsCertificate $graph) ← liftExcept <| componentsCertificateOfJson graph componentsCertificateJ
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := componentsCertificateName
    levelParams := []
    type := q(ComponentsCertificate $graph)
    value := componentsCertificateQ
    hints := .regular 0
    safety := .safe
  }

#loadHog "hog00001"
#eval (hog00001.edgeSizeI.val)


-- elab "getHog" hogId:str : term => do
--   let hog := hogName hogId.getString
--   let env ← Lean.getEnv
--   match env.contains hog with
--   | true => pure (Lean.mkConst hog [])
--   | false => loadHog hogId ; pure (Lean.mkConst hog [])

end HoG
