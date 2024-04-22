import LeanHoG.LoadGraph
import LeanHoG.Graph
import LeanHoG.Invariant.ConnectedComponents.Basic
import Qq

namespace LeanHoG

-- We cannot use a function as it refuses to call a command
def verifGraphFunc : IO Unit := do
  let files ← System.FilePath.readDir "graphs"
  for file in files do
    load_graph G file.path.toString

-- In order to create a command, we should define a syntax?
syntax (name := verifGraphs) "verify" : command

-- This command is the same as the function above but still cannot call another command
@[command_elab verifGraph]
def verifGrahpImpl : IO Unit
  | `(verify) => do
  let files ← System.FilePath.readDir "graphs"
  for file in files do
    load_graph G file.path.toString
  | _ => Lean.Elab.throwUnsupportedSyntax

-- This function will directly call the one used by load_graph
unsafe def verifGraphCall : IO Unit := do
  let files ← System.FilePath.readDir "testgraphs"
  for file in files do
    -- loadGraphAux takes a Name so we need to create one.
    let name := Lean.Name.mkSimple "G"
    let jsonData ← loadJSONData JSONData file.path.toString
    -- Because we are in the IO monad and loadGraphAux returns a CommandElab, we cannot use the arrow syntax?
    match loadGraphAux name jsonData with
    | _ =>
      -- If we could get the actual variable behind the name, we could do the checking. But here, we only have a name of type Name.
      IO.println name
      pure ()

syntax (name := verifGraphsCalling) "verify_call" : command

open Qq
-- I try to do the same as above using a command. Maybe here I can somehow do something with the name.
@[command_elab verifGraphsCalling]
unsafe def verifGraphCallingImpl : Lean.Elab.Command.CommandElab
  | `(verify_call) => do
  let files ← System.FilePath.readDir "testgraphs"
  for file in files do
    let jsonData ← loadJSONData JSONData file.path.toString
    let name := Lean.Name.mkSimple "H"
    match loadGraphAux name jsonData with
    |  _ => do
      have graph : Q(Graph) := Lean.mkConst name
      let check := q(IO.println ($graph).is_connected)
  | _ => Lean.Elab.throwUnsupportedSyntax

load_graph G "graphs/660.json"
#eval G.numberOfConnectedComponents

#eval verifGraphCall

verify_call
