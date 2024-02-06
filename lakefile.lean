import Lake
open Lake DSL

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LeanHoG
