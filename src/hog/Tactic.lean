import Mathlib.Init.Data.Bool.Lemmas

namespace LeanHog.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

syntax "bool_reflect" : tactic
macro_rules
| `(tactic| bool_reflect) => `(tactic| apply Bool.of_decide_true; rfl)


end LeanHog.Tactic