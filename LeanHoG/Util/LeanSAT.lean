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

/--
Resource limits for one external solver invocation.

Both matter for different reasons. `timeoutSec` bounds a solver that spins
without producing much proof; `maxProofBytes` bounds one that produces proof
very fast. Only the second protects the disk: an undecidable instance can emit
LRAT at tens of MB/s, so a generous time limit alone still permits many GB.
-/
structure SolverLimits where
  /-- Wall-clock limit in seconds handed to the solver via `-t`. `0` disables. -/
  timeoutSec : Nat := 300
  /-- Hard cap on the certificate; the solver is killed past it. `0` disables. -/
  maxProofBytes : Nat := 1024 * 1024 * 1024
  deriving Inhabited

/-- Size of `path` in bytes, or `0` if it cannot be stat'd (e.g. not created yet). -/
private def fileSizeOrZero (path : System.FilePath) : IO Nat := do
  try
    return (← path.metadata).byteSize.toNat
  catch _ =>
    return 0

/--
Poll the growing certificate and kill the solver if it passes `maxBytes`.

Returns as soon as `finished` is set, so the caller can join it once the solver
exits. Sets `tripped` before killing, so the caller can tell "killed by us" from
"exited on its own".
-/
private partial def watchProofSize
    (killSolver : IO Unit) (proof : System.FilePath) (maxBytes : Nat)
    (finished tripped : IO.Ref Bool) : IO Unit := do
  if maxBytes == 0 then return
  if ← finished.get then return
  IO.sleep 200
  if ← finished.get then return
  if (← fileSizeOrZero proof) > maxBytes then
    tripped.set true
    killSolver
  else
    watchProofSize killSolver proof maxBytes finished tripped

def SolverWithLRAT (solverCmd : String) (solverFlags : Array String := #[])
    (limits : SolverLimits := {}) : Solver IO where
  solve := fun fml => IO.FS.withTempFile fun _ tempFile => do
    let timeoutFlags :=
      if limits.timeoutSec == 0 then #[] else #["-t", toString limits.timeoutSec]
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := solverFlags ++ timeoutFlags ++ #["-", tempFile.toString]
      stdin := .piped
      stdout := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    writeDimacs stdin fml
    stdin.flush

    -- Watch the certificate only once the formula is in; nothing is written before that.
    let finished ← IO.mkRef false
    let tripped ← IO.mkRef false
    let watchdog ← IO.asTask
      (watchProofSize solver.kill tempFile limits.maxProofBytes finished tripped)
      Task.Priority.dedicated

    let output ← IO.asTask solver.stdout.readToEnd Task.Priority.dedicated

    let exitCode ← solver.wait
    finished.set true
    -- Join the watchdog before leaving the temp-file scope, so nothing is still
    -- stat'ing a path `withTempFile` is about to remove. Its own errors are
    -- uninteresting: `kill` races the solver exiting on its own.
    match watchdog.get with
    | .ok _ => pure ()
    | .error _ => pure ()

    if ← tripped.get then
      throw <| IO.userError <|
        s!"SAT solver killed: its LRAT certificate passed the \
           {limits.maxProofBytes / (1024 * 1024)} MB cap. This instance is too hard \
           for the current pipeline; raise `leanHoG.maxCertificateSize` (in MB) to \
           allow more, or 0 to remove the cap entirely — but note an undecidable \
           instance will then write until the disk is full."

    -- 10 = SAT, 20 = UNSAT, by SAT-competition convention. Anything else means the
    -- solver stopped without deciding, which on this path is the `-t` limit. Note
    -- cadical prints *no* `s` line at all when it times out, so the exit code is
    -- the only usable signal — do not try to parse the output for this.
    if exitCode != 10 && exitCode != 20 then
      throw <| IO.userError <|
        s!"SAT solver stopped without deciding (exit {exitCode}); it most likely hit \
           its {limits.timeoutSec}s time limit. Raise `leanHoG.solverTimeout` \
           (in seconds, 0 for none) to allow more."

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
