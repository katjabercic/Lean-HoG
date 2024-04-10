import Lake
open Lake DSL

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.0"

require «lean-sat» from git
  "https://github.com/cilinder/LeanSAT.git" @ "cake-lpr"

-- You should replace v0.0.3 with the latest version published under Releases
require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4"@"v0.0.29"

lean_lib LeanHoG

lean_exe build_widgets where
  root := `widget.Build

def npmCmd : String :=
  if System.Platform.isWindows then "npm.cmd" else "npm"

def widgetDir := __dir__ / "widget"

def widgetBuildAll (_ : NPackage _package.name) :
  IndexBuildM (BuildJob (Array FilePath)) := do

  let job := (Task.spawn (fun () => do
    let output1 ← IO.Process.output {
      cwd := "widget"
      cmd := npmCmd
      args := #["install", "--silent", "--no-progress"]
    }
    if output1.exitCode ≠ 0 then
      IO.eprintln s!"failed to install npm packages: {output1.stderr}"
      return
    let output2 ← IO.Process.output {
      cwd := "widget"
      cmd := npmCmd
      args := #["run", "build"]
    }
    if output2.exitCode ≠ 0 then
      IO.eprintln s!"failed to run npm build: {output2.stderr}"
  ))
  Task.get job
  BuildJob.collectArray #[]

target buildWidget pkg : Array FilePath := do
  widgetBuildAll pkg

@[default_target]
target all : Unit := do
  let lib ← LeanHoG.get
  let job₁ ← buildWidget.fetch
  let _ ← job₁.await
  let job₂ ← lib.leanArts.fetch
  let _ ← job₂.await
  return .nil
