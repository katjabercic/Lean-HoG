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

/--
`IO.Process.Child.wait` reports a child killed by a signal as `128 + signum`,
so the two exit codes we can attribute to a definite cause are both signals.
-/
private def signalExit (signum : Nat) : UInt32 := UInt32.ofNat (128 + signum)

/--
`SIGALRM`. cadical implements `-t` with `alarm`, and on the path we use — the
formula arriving on stdin — the handler is not installed by the time it fires, so
the limit kills the process outright instead of exiting cleanly with `0` and
`UNKNOWN`. That makes 142, not 0, our timeout code. See issue #58.
-/
private def exitTimeLimit : UInt32 := signalExit 14

/-- `SIGTERM`, which is what `watchProofSize` sends when the certificate cap trips. -/
private def exitKilled : UInt32 := signalExit 15

/--
Lean's forked child reports a failed `exec` — no such binary, or not executable —
as this, having written its own complaint to stderr. It is not a solver code.
-/
private def exitExecFailed : UInt32 := 255

/-- The solver's own stderr as a block to append to an error, or nothing if it was quiet. -/
private def diagnostics (stderr : String) : String :=
  let stderr := stderr.trimAscii
  if stderr.isEmpty then "" else s!"\n\nThe solver wrote:\n{stderr}"

def SolverWithLRAT (solverCmd : String) (solverFlags : Array String := #[])
    (limits : SolverLimits := {}) : Solver IO where
  solve := fun fml => IO.FS.withTempFile fun _ tempFile => do
    let timeoutFlags :=
      if limits.timeoutSec == 0 then #[] else #["-t", toString limits.timeoutSec]
    let args := solverFlags ++ timeoutFlags ++ #["-", tempFile.toString]
    -- The invocation as a single line, for the unrecognised-exit-code error below.
    -- Built from the same `args` that are spawned, so what we quote back cannot
    -- drift from what ran: the flags come from three places at once and the user
    -- wrote at most one of them, so naming the option they came from is no help.
    let call := " ".intercalate (solverCmd :: args.toList)
    let solver ← IO.Process.spawn {
      cmd := solverCmd
      args := args
      stdin := .piped
      stdout := .piped
      -- Piped, not inherited: an unpositioned line on Lean's own stderr is
      -- invisible in the editor, and the solver's complaint is usually the whole
      -- explanation. It is read below and folded into whatever we throw.
      stderr := .piped
    }
    let (stdin, solver) ← solver.takeStdin
    -- A solver that is already gone makes this fail with EPIPE. Hold that rather
    -- than letting a bare "resource vanished" escape: the exit code collected
    -- below says *why* it went, which is the part worth reporting.
    let writeFailed ←
      try
        writeDimacs stdin fml
        stdin.flush
        pure false
      catch _ => pure true

    -- Watch the certificate only once the formula is in; nothing is written before that.
    let finished ← IO.mkRef false
    let tripped ← IO.mkRef false
    let watchdog ← IO.asTask
      (watchProofSize solver.kill tempFile limits.maxProofBytes finished tripped)
      Task.Priority.dedicated

    -- Both pipes are drained concurrently: a solver that fills one while we block
    -- on the other would deadlock.
    let output ← IO.asTask solver.stdout.readToEnd Task.Priority.dedicated
    let errOutput ← IO.asTask solver.stderr.readToEnd Task.Priority.dedicated

    let exitCode ← solver.wait
    finished.set true
    -- Join the watchdog before leaving the temp-file scope, so nothing is still
    -- stat'ing a path `withTempFile` is about to remove. Its own errors are
    -- uninteresting: `kill` races the solver exiting on its own.
    match watchdog.get with
    | .ok _ => pure ()
    | .error _ => pure ()

    -- Never fails the run on its own account: this is only ever decoration for an
    -- error we are already about to throw.
    let diag :=
      match errOutput.get with
      | .ok s => diagnostics s
      | .error _ => ""

    if ← tripped.get then
      throw <| IO.userError <|
        s!"SAT solver killed: its LRAT certificate passed the \
           {limits.maxProofBytes / (1024 * 1024)} MB cap. This instance is too hard \
           for the current pipeline; raise `leanHoG.maxCertificateSize` (in MB) to \
           allow more, or 0 to remove the cap entirely — but note an undecidable \
           instance will then write until the disk is full.{diag}"

    -- The solver died mid-formula. Reached before the exit-code cases below because
    -- it did not see the whole problem, so its code says nothing about the instance.
    if writeFailed then
      if exitCode == exitTimeLimit && limits.timeoutSec != 0 then
        throw <| IO.userError <|
          s!"SAT solver hit its {limits.timeoutSec}s time limit while Lean was still \
             writing the formula, so it never saw the whole problem. `-t` starts \
             counting when the solver launches, not when the formula is complete, and \
             for a large graph the write alone can outlast it. Raise \
             `leanHoG.solverTimeout` (in seconds, 0 for none).{diag}"
      else
        throw <| IO.userError <|
          s!"SAT solver exited (exit {exitCode}) before Lean finished writing the \
             formula to it.{diag}"

    if exitCode == exitExecFailed then
      throw <| IO.userError <|
        s!"Could not run the SAT solver `{solverCmd}` (exit {exitCode}). Check that \
           `leanHoG.solverCmd` names a solver that is on `PATH` and executable.{diag}"

    if exitCode == exitTimeLimit && limits.timeoutSec != 0 then
      throw <| IO.userError <|
        s!"SAT solver hit its {limits.timeoutSec}s time limit without deciding \
           (exit {exitCode}). Raise `leanHoG.solverTimeout` (in seconds, 0 for none) \
           to allow more.{diag}"

    if exitCode == exitKilled && limits.maxProofBytes != 0 then
      throw <| IO.userError <|
        s!"SAT solver was killed by SIGTERM (exit {exitCode}) without deciding. That is \
           what the `leanHoG.maxCertificateSize` watchdog sends, so its certificate most \
           likely passed the {limits.maxProofBytes / (1024 * 1024)} MB cap just as the \
           solver was exiting anyway.{diag}"

    -- 10 = SAT, 20 = UNSAT, by SAT-competition convention. Anything else means the
    -- solver stopped without deciding, and having exhausted the codes we can name,
    -- we report rather than guess. Note cadical prints *no* `s` line when it stops
    -- early, so the exit code is the only usable signal — do not parse the output.
    if exitCode != 10 && exitCode != 20 then
      throw <| IO.userError <|
        s!"SAT solver stopped without deciding (exit {exitCode}), for a reason this \
           pipeline does not recognise. The call was:\n  {call}{diag}"

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
