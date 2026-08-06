import Lake

open Lake DSL System

package «LeanHoG» {
  moreLeanArgs := #["-DautoImplicit=false"]
}

-- Pinned to a commit on trestle's `dev` branch: 4.28 support is not in a
-- released version yet. Pin, don't track the branch, so builds stay
-- reproducible. See issue #53 for moving back to a release.
require «trestle» from git "https://github.com/FormalSAT/trestle.git" @ "853ce034ff4a5081d19ccc250d5780d4b7e718ec"

require «mdgen» from git "https://github.com/Seasawher/mdgen.git" @ "v4.28.0-rc1"

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

lean_lib Examples where
  needs := #[LeanHoG]

lean_exe examples_md where
  root := `ExamplesMD
