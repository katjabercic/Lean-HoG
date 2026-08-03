import Trestle
import Trestle.Solver.Basic
import Trestle.Solver.Dimacs
import Trestle.Solver.Impl.DimacsCommand
import LeanHoG.Util.TrestleStd
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Trestle

def runLRATChecker (fml : ICnf) (proof : System.FilePath) : IO Bool :=
  do
    let actions ← Std.Tactic.BVDecide.LRAT.loadLRATProof proof
    -- Converting the CNF and checking the parsed actions are pure computations.
    let stdCnf := fml.toStd
    return Std.Tactic.BVDecide.LRAT.check actions stdCnf

def SolverWithLRAT (solverCmd : String) (solverFlags : Array String := #[]) : Solver IO where
  solve := fun fml => do
    let tempFile := "proof.lrat"
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := solverFlags ++ #["-", tempFile]
      stdin := .piped
      stdout := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    Solver.Dimacs.printICnf (stdin.putStr) fml
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
      let succeeded ← runLRATChecker fml tempFile
      IO.FS.removeFile tempFile
      if succeeded then
        return res
      else
        return .error
    | .sat assn =>
      IO.FS.removeFile tempFile
      return (.sat assn)
