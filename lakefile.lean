import Lake
open Lake DSL

package «JSON2Lean» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib JSON2Lean
