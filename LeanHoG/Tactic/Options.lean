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

register_option leanHoG.cake_lprCmd : String := {
  defValue := "cake_lrp"
  descr := "The location of a cake_lpr executable used for checking unsat proofs"
}

register_option leanHoG.graphDownloadLocation : String := {
  defValue := "build/graphs"
  group := "pp"
  descr := "Location for storing downloaded graphs and search results"
}

register_option leanHoG.searchCacheLocation : String := {
  defValue := "build/search_results"
  group := "pp"
  descr := "Location for caching search results"
}
