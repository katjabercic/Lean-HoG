import Lake
open Lake DSL

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

require «lean-sat» from git
  "https://github.com/cilinder/LeanSAT.git" @ "alt"

@[default_target]
lean_lib LeanHoG

lean_lib Convert
lean_lib js

lean_exe get_graphs where
  root := `Convert.GetGraphs

lean_exe build_widgets where
  root := `js.Build

post_update pkg do
  let exitCode ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "build_widgets"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    logError s!"{pkg.name}: failed to build widgets"
