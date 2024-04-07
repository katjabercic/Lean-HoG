import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  group := "pp"
  descr := "The python executable location for external calls"
}

register_option leanHoG.downloadLocation : String := {
  defValue := "build"
  group := "pp"
  descr := "Location for storing downloaded graphs and search results"
}
