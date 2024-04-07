import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  group := "pp"
  descr := "The python executable location for external calls"
}

register_option leanHoG.cadicalCmd : String := {
  defValue := "cadical"
  descr := "The location of a cadical executable to run the SAT problems"
}

register_option leanHoG.cake_lprCmd : String := {
  defValue := "cake_lrp"
  descr := "The location of a cake_lpr executable used for checking unsat proofs"
}
