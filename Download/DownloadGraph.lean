import LeanHoG.Util.IO

def usage :=
"Usage: lake exe get_graphs <min-id> <max-id>
Download graphs with in the given id range from the House of Graphs"

def Option.toIntOpt : Option String -> Option Int
  | none => none
  | some s => s.toInt?

def main (args : List String) : IO Unit := do
  if args.length < 1 then
    IO.eprintln "Invalid parameters"
    IO.println usage
    return
  let pythonExe ← IO.findPythonExecutable -- Hacky solution, can we make into user option?
  let downloadLocation := "build/graphs"
  match args[0]!.toInt?, args[1]?.toIntOpt with
  | some a, some b =>
    let exitCode ← IO.Process.spawn {
      cmd := pythonExe
      args := #["Download/downloadGraphs.py", downloadLocation, s!"{a}", s!"{b}"]
    } >>= (·.wait)
    if exitCode ≠ 0 then
      IO.eprintln s!"failed to download graphs"
  | some a, none =>
    let exitCode ← IO.Process.spawn {
      cmd := pythonExe
      args := #["Download/downloadGraphs.py", downloadLocation, s!"{a}", s!"{a}"]
    } >>= (·.wait)
    if exitCode ≠ 0 then
      IO.eprintln s!"failed to download graphs"
  | _, _ =>
    IO.eprintln "Invalid parameters"
    IO.println usage
