import Lean
import Qq
import LeanHoG.Certificate
import LeanHoG.Examples

namespace LeanHoG

-- initialize cow : GraphCertificate ← loadGraphCertificate "cert.json"
-- #eval cow

def decForallFin {α : Type} {n : Nat} {p : Fin n → Prop} [DecidablePred p] :
    Decidable (∀ (k : Fin n), p k) :=
  match n with
  | 0 => isTrue (by
                  intro k
                  cases k
                    )
  | .succ n => _


structure Dog (n : Nat) extends Cow where
  (good : ∀ k : Fin n, Nat.blt (next k) (next (k + 1)) := by decide)

def bessie : Cow := { next := fun k => k + 1 }

def bessieJ : Lean.Json :=
  match Lean.Json.parse "{ \"foo\" : 6 }" with
  | .ok j => j
  | .error _ => .null

end LeanHoG


elab "load_rbset" name:ident filename:str : command => do
  let treeName := name.getId
  let data ← LeanHoG.loadGAPData filename.getString
  have vertexSize : Q(Nat) := Lean.mkRawNatLit data.graph.vertexSize
  have linOrder : Q(LinearOrder (LeanHoG.Edge $vertexSize)) := q(LeanHoG.Edge.linearOrder)
  have arrQ : Array Q(LeanHoG.Edge $vertexSize) := data.graph.edges.map (LeanHoG.edgeOfData vertexSize)
  have treeQ : Q(Std.RBSet (LeanHoG.Edge $vertexSize) $(linOrder).compare) := build_RBSet arrQ q($linOrder)
  Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
    name := treeName
    levelParams := []
    type := q(Std.RBSet (LeanHoG.Edge $vertexSize) ($linOrder).compare)
    value := q($treeQ)
    hints := .regular 0
    safety := .safe
  }


elab "load_rbmap" name:ident filename:str : command => do
  let treeName := name.getId
  let data ← LeanHoG.loadGAPData filename.getString
  match data.connectivityData? with
  | .none => pure ()
  | .some data =>
    have linOrder : Q(LinearOrder ℕ) := q(Nat.linearOrder)
    have arrQ : Array Q(ℕ × ℕ) := data.next.map (fun (i,j) => (q(($i, $j))))
    have treeQ : Q(Std.RBMap ℕ ℕ $(linOrder).compare) := build_RBMap arrQ q($linOrder)
    Lean.Elab.Command.liftCoreM <| Lean.addAndCompile <| .defnDecl {
      name := treeName
      levelParams := []
      type := q(Std.RBMap ℕ ℕ ($linOrder).compare)
      value := q($treeQ)
      hints := .regular 0
      safety := .safe
    }

load_rbset Set1 "examples/cube5.json"
load_rbmap Map1 "examples/cube5.json"

#check Set1
#eval Set1

#check Map1
#eval Map1.find! 6
