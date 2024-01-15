import Lake
open Lake DSL

package «HoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0-rc2"

require «lean-sat» from git
  "https://github.com/JamesGallicchio/LeanSAT.git" @ "dev"

@[default_target]
lean_lib HoG
