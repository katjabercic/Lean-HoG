import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  group := "pp"
  descr := "The python executable location for external calls"
}

register_option leanHoG.solverCmd : String := {
  defValue := "cadical"
  descr := "The location of a solver executable to run the SAT problems"
}

register_option leanHoG.proofCheckerCmd : String := {
  defValue := "cake_lpr"
  descr := "The location of a proof checker executable used for checking unsat proofs.
  The checker should except LRAT proofs."
}

register_option leanHoG.graphDownloadLocation : String := {
  defValue := "build/graphs"
  group := "pp"
  descr := "Location for storing downloaded graphs"
}

register_option leanHoG.searchCacheLocation : String := {
  defValue := "build/search_results"
  group := "pp"
  descr := "Location for caching search results"
}
