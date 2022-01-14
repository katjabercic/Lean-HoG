import system.io
import data.fin
open expr tactic
open interactive (parse)
open interactive.types (texpr)
namespace python
meta def buffered_cmd (args : io.process.spawn_args) (input : char_buffer) : io char_buffer :=
do
  child ← io.proc.spawn {args with stdout := io.process.stdio.piped, stdin := io.process.stdio.piped},
  io.fs.write child.stdin input,
  io.fs.close child.stdin,
  buf ← io.fs.read_to_end child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process failed with status" ++ to_string exitv,
  return buf 

meta def run (arg : string) (input : char_buffer) : tactic char_buffer :=
let cmd' := "python3",
    s_args := {io.process.spawn_args. cmd := cmd', args := [arg]} in
do
  c ← tactic.unsafe_run_io $ io.env.get_cwd,
  tactic.unsafe_run_io $ buffered_cmd s_args input

end python