import Lean
import Qq
import JSON2Lean.Certificate
import JSON2Lean.Examples

namespace JSON2Lean

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

end JSON2Lean
