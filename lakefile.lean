import Lake
open Lake DSL System

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

require «trestle» from git "https://github.com/FormalSAT/trestle.git" @ "853ce03"

def widgetDir : FilePath := "widget"

nonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=
  pkg.dir / widgetDir

def Lake.Package.runNpmCommand (pkg : Package) (args : Array String) : LogIO Unit :=
  if Platform.isWindows then
    proc {
      cmd := "powershell"
      args := #["-Command", "npm.cmd"] ++ args
      cwd := pkg.widgetDir
    } (quiet := true)
  else
    proc {
      cmd := "npm"
      args
      cwd := pkg.widgetDir
    } (quiet := true)

input_file widgetPackageJson where
  path := widgetDir / "package.json"
  text := true

input_file widgetPackageLock where
  path := widgetDir / "package-lock.json"
  text := true

input_file widgetRollupConfig where
  path := widgetDir / "rollup.config.js"
  text := true

input_dir widgetSrcs where
  path := widgetDir / "src"
  filter := .extension <| .mem #["js", "jsx"]
  text := true

target buildWidget pkg : Unit := do
  let srcs ← widgetSrcs.fetch
  let config ← widgetRollupConfig.fetch
  let packageJson ← widgetPackageJson.fetch
  let packageLock ← widgetPackageLock.fetch
  srcs.bindM (sync := true) fun _ =>
  config.bindM (sync := true) fun _ =>
  packageJson.bindM (sync := true) fun _ =>
  packageLock.mapM fun _ => do
    let outputFile := pkg.dir / "build" / "js" / "graphVisualization.js"
    buildUnlessUpToDate outputFile (← getTrace) (outputFile.addExtension "trace") do
      pkg.runNpmCommand #["clean-install", "--silent", "--no-progress"]
      pkg.runNpmCommand #["run", "build"]

@[default_target]
lean_lib LeanHoG where
  needs := #[buildWidget]

-- This is only to get the command "lake build verify" to build Verify.lean
-- This way, there is no need to open the file in an editor.
lean_lib verify where
  srcDir := "."
  roots := #[`Verify]
