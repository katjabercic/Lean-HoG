def main : IO Unit := do
  let exitCode ← IO.Process.spawn {
    cwd := "js"
    cmd := "npm"
    args := #["install", "--silent", "--no-progress"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    IO.eprintln s!"failed install npm packages"

  let exitCode ← IO.Process.spawn {
    cwd := "js"
    cmd := "npm"
    args := #["run", "build"]
  } >>= (·.wait)
  if exitCode ≠ 0 then
    IO.eprintln s!"failed to run npm build"
