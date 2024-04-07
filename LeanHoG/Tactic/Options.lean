import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  group := "pp"
  descr := "The python executable location for external calls"
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
