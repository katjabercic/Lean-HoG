import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  descr := "The python executable location for external calls"
}

register_option leanHoG.solverCmd : String := {
  defValue := "cadical"
  descr := "The location of a solver executable to run the SAT problems"
}

register_option leanHoG.graphDownloadLocation : String := {
  defValue := "build/graphs"
  descr := "Location for storing downloaded graphs"
}

register_option leanHoG.searchCacheLocation : String := {
  defValue := "build/search_results"
  descr := "Location for caching search results"
}
