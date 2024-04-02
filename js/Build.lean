import Init.System.Platform


def main : IO Unit := do
  let npmCmd : String :=
    if System.Platform.isWindows then "npm.cmd" else "npm"
  let exitCode ← IO.Process.spawn {
    cwd := "js"
    cmd := npmCmd
    args := #["install", "--silent", "--no-progress"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    IO.eprintln s!"failed to install npm packages"
    return
  let exitCode ← IO.Process.spawn {
    cwd := "js"
    cmd := npmCmd
    args := #["run", "build"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    IO.eprintln s!"failed to run npm build"
