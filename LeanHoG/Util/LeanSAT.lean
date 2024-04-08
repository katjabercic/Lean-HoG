import LeanSAT
import LeanSAT.Solver.Basic
import LeanSAT.Solver.Dimacs

import LeanSAT.Util.MkFIFO

namespace SolverWithCakeLpr

open LeanSAT

def runCakeLpr (cake_lpr : String := "cake_lpr") (fml : ICnf) (proof : System.FilePath)
    : IO Bool :=
  Util.withTempFIFO fun cnfPath => do
  let cakeProc ← IO.Process.spawn {
    cmd := cake_lpr
    args := #[cnfPath.toString, proof.toString]
    stdout := .piped
  }
  -- Note: opening a FIFO file to write blocks until someone opens the FIFO file to read
  let cnfHandle ← IO.FS.Handle.mk cnfPath .write
  Solver.Dimacs.printFormula (cnfHandle.putStr) fml
  cnfHandle.flush
  let output ← IO.asTask cakeProc.stdout.readToEnd Task.Priority.dedicated
  let _ ← cakeProc.wait
  let outputStr ← IO.ofExcept output.get
  return outputStr.trim = "s VERIFIED UNSAT"

def SolverWithCakeLpr (solverCmd : String) (solverFlags : Array String := #[]) (cakelprCmd : String := "cake_lpr") : LeanSAT.Solver IO where
  solve := fun fml => do
    let tempFile := "proof.lrat"
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := solverFlags ++ #["-", tempFile]
      stdin := .piped
      stdout := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    Solver.Dimacs.printFormula (stdin.putStr) fml
    stdin.flush
    let output ← IO.asTask solver.stdout.readToEnd Task.Priority.dedicated

    let _ ← solver.wait
    let outputStr ← IO.ofExcept output.get
    let res ← IO.ofExcept <| Solver.Dimacs.parseResult fml.maxVar outputStr
    match res with
    | .error =>
      IO.FS.removeFile tempFile
      return .error
    | .unsat =>
      let succeeded ← runCakeLpr cakelprCmd fml tempFile
      IO.FS.removeFile tempFile
      if succeeded then
        return res
      else
        return .error
    | .sat assn =>
      IO.FS.removeFile tempFile
      return (.sat assn)

end SolverWithCakeLpr
