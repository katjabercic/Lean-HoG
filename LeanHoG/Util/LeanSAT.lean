import Trestle
import Trestle.Solver.Basic
import Trestle.Solver.Dimacs
import Trestle.Solver.Impl.DimacsCommand
import LeanHoG.Util.TrestleStd
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Trestle

private partial def writeDimacsClauses
    (stream : IO.FS.Handle) (fml : ICnf) (i : Nat) : IO Unit := do
  if h : i < fml.size then
    stream.putStr (Trestle.Solver.Dimacs.formatClause fml[i] ++ "\n")
    writeDimacsClauses stream fml (i + 1)

private def writeDimacs (stream : IO.FS.Handle) (fml : ICnf) : IO Unit := do
  stream.putStr s!"p cnf {fml.maxVar} {fml.size}\n"
  writeDimacsClauses stream fml 0

def runLRATChecker (fml : ICnf) (proof : System.FilePath) : IO Bool :=
  do
    let actions ← Std.Tactic.BVDecide.LRAT.loadLRATProof proof
    -- Converting the CNF and checking the parsed actions are pure computations.
    let stdCnf := fml.toStd
    return Std.Tactic.BVDecide.LRAT.check actions stdCnf

def SolverWithLRAT (solverCmd : String) (solverFlags : Array String := #[]) : Solver IO where
  solve := fun fml => IO.FS.withTempFile fun _ tempFile => do
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := solverFlags ++ #["-", tempFile.toString]
      stdin := .piped
      stdout := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    writeDimacs stdin fml
    stdin.flush
    let output ← IO.asTask solver.stdout.readToEnd Task.Priority.dedicated

    let _ ← solver.wait
    let outputStr ← IO.ofExcept output.get
    let res ← IO.ofExcept <| Solver.Dimacs.parseResult fml.maxVar outputStr
    match res with
    | .error => return .error
    | .unsat =>
      let succeeded ← runLRATChecker fml tempFile
      if succeeded then
        return res
      else
        return .error
    | .sat assn => return (.sat assn)
