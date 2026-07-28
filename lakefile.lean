import Lake
open Lake DSL

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require «trestle» from git "https://github.com/FormalSAT/trestle.git" @ "853ce03"

lean_lib LeanHoG where
  extraDepTargets := #[`buildWidget]

lean_exe build_widgets where
  root := `widget.Build

def npmCmd : String :=
  if System.Platform.isWindows then "npm.cmd" else "npm"

def widgetDir := __dir__ / "widget"

def widgetBuildAll (_ : NPackage __name__) :
  FetchM (Job (Array System.FilePath)) := do

  let job := (Task.spawn (fun () => do
    let output1 ← IO.Process.output {
      cwd := widgetDir
      cmd := npmCmd
      args := #["install", "--silent", "--no-progress"]
    }
    if output1.exitCode ≠ 0 then
      IO.eprintln s!"failed to install npm packages: {output1.stderr}"
      return
    let output2 ← IO.Process.output {
      cwd := widgetDir
      cmd := npmCmd
      args := #["run", "build"]
    }
    if output2.exitCode ≠ 0 then
      IO.eprintln s!"failed to run npm build: {output2.stderr}"
  ))
  Task.get job
  return Job.collectArray #[]

target buildWidget pkg : Array System.FilePath := do
  widgetBuildAll pkg

@[default_target]
target all : Unit := do
  let lib ← LeanHoG.get
  let job₁ ← buildWidget.fetch
  let _ ← job₁.await
  let job₂ ← lib.leanArts.fetch
  let _ ← job₂.await
  return .nil
