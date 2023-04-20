import Lean
import Qq

set_option autoImplicit false

namespace Experiment

structure Edge (n : Nat) : Type :=
  edge ::
  fst : Fin n
  snd : Fin fst
deriving Repr

@[simp]
def nat_compare (i j : Nat) : Ordering :=
  if i < j then .lt else (if i = j then .eq else .gt)

@[simp]
def Edge.compare {m : Nat} (u v : Edge m) : Ordering :=
  match nat_compare u.fst v.fst with
  | .lt => .lt
  | .eq => nat_compare u.snd v.snd
  | .gt => .gt

@[simp]
instance Edge_Ord (m : Nat): Ord (Edge m) where
  compare := Edge.compare

inductive Tree (α : Type) : Type
  | empty : Tree α
  | leaf : α → Tree α
  | node : α → Tree α → Tree α → Tree α

def Edge.mk' (n a b : Nat) (H : Nat.blt a n = true) (H2 : Nat.blt b a = true) : Edge n :=
  ⟨⟨a, by simp_all⟩, ⟨b, (by simp_all : b < a)⟩⟩

open Qq Lean Meta Elab

def mkEdge (n : Q(Nat)) (j : Json) : Except String Q(Edge $n) := do
  let arr ← j.getArr?
  have a : Q(Nat) := mkRawNatLit (← arr[0]!.getNat?)
  have b : Q(Nat) := mkRawNatLit (← arr[1]!.getNat?)
  have H : Q(Nat.blt $a $n = true) := (q(Eq.refl true) : Expr)
  have H2 : Q(Nat.blt $b $a = true) := (q(Eq.refl true) : Expr)
  pure q(Edge.mk' $n $a $b $H $H2)

partial def mkTree (n : Q(Nat)) (j : Json) : Except String Q(Tree (Edge $n)) := do
  let arr ← j.getArr? 
  match arr with
  | #[e, l, r] => pure q(Tree.node $(← mkEdge n e) $(← mkTree n l) $(← mkTree n r))
  | #[] => pure q(Tree.empty)
  | #[v] => pure q(Tree.leaf $(← mkEdge n v))
  | _ => throw "invalid tree format"

elab "tree_from_file" name:ident " from " file:str : command => do
  let file ← IO.FS.readFile file.getString
  let result : Except String (Q(Nat) × Expr) := do
    let json ← Json.parse file
    let njson ← json.getObjVal? "vertexSize"
    let n : Q(Nat) := mkRawNatLit (← njson.getNat?)
    let tree ← (mkTree n (← json.getObjVal? "edges"))
    pure (n, tree)
  match result with
  | .error msg => throwError msg
  | .ok (n, value) =>
    Elab.Command.liftCoreM <| addDecl <| .defnDecl {
      name := name.getId
      levelParams := []
      type := q(Tree (Edge $n))
      value
      hints := .regular 0
      safety := .safe
    }

-- tree_from_file test from "/Users/andrej/Documents/Lean-HoG/src/hog/example.json"
-- #check test -- test : Tree (Edge 666)

end Experiment