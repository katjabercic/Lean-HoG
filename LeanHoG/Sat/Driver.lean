import LeanHoG.Tactic.Options
import LeanHoG.Util.LeanSAT

/-!
# Running the SAT solver from a tactic

The elaborator side of the SAT pipeline: turning user options into a configured solver.
`LeanHoG.Util.LeanSAT` holds the solver itself, which knows nothing about Lean options.
-/

namespace LeanHoG

open Lean Trestle

/-- How to run the solver, as the user's options ask for it.

The command name is kept alongside the limits because a search that gets an answer it
cannot use quotes it back: when the solver reports SAT with an assignment that is not a
Hamiltonian path, naming the command that produced it is the whole content of the error. -/
structure SolverConfig where
  /-- The solver to run, from `leanHoG.solverCmd`. -/
  cmd : String
  /-- Time and certificate-size limits, from `leanHoG.solverTimeout` and
      `leanHoG.maxCertificateSize`. -/
  limits : SolverLimits

/-- Read `leanHoG.solverCmd`, `leanHoG.solverTimeout` and `leanHoG.maxCertificateSize`.

This is deliberately not the solver itself: `Trestle.Solver IO` is a `Type 1`, and `CoreM`
quantifies over `Type`, so the solver cannot be returned from a monadic action here. Reading
the configuration and building the solver from it are therefore two steps — see
`SolverConfig.solver`. -/
def solverConfig : CoreM SolverConfig := do
  let opts ← getOptions
  return {
    cmd := opts.get leanHoG.solverCmd.name leanHoG.solverCmd.defValue
    limits := {
      timeoutSec := opts.get leanHoG.solverTimeout.name leanHoG.solverTimeout.defValue
      maxProofBytes :=
        opts.get leanHoG.maxCertificateSize.name leanHoG.maxCertificateSize.defValue
          * 1024 * 1024
    }
  }

/-- The solver this configuration describes.

The flags are not a detail of the caller: `SolverWithLRAT` reads back an LRAT certificate
and hands it to Lean's checker, which `--lrat=true` is what produces and `--no-binary` is
what keeps parseable. A caller that passed its own flags could silently disable the checking
the whole pipeline rests on. -/
def SolverConfig.solver (c : SolverConfig) : Solver IO :=
  SolverWithLRAT c.cmd #["--no-binary", "--lrat=true"] c.limits

end LeanHoG
