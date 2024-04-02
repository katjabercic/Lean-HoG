
def IO.findPythonExecutable : IO String := do
  let output ← IO.Process.output {
    cmd := "python"
    args := #["--version"]
  }
  if output.exitCode ≠ 0 then
    let output ← IO.Process.output {
      cmd := "python3"
      args := #["--version"]
    }
    if output.exitCode ≠ 0 then
      throw <| IO.userError output.stderr
    else
      return "python3"
  else
    return "python"
