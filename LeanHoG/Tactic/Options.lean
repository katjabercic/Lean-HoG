import Lean

register_option leanHoG.pythonExecutable : String := {
  defValue := "python"
  descr := "The python executable location for external calls"
}

register_option leanHoG.solverCmd : String := {
  defValue := "cadical"
  descr := "The location of a solver executable to run the SAT problems"
}

register_option leanHoG.solverTimeout : Nat := {
  defValue := 300
  descr := "Wall-clock limit in seconds for a single SAT solver invocation. \
            0 disables the limit. Every graph measured so far that the solver \
            actually decided finished well under 120s."
}

register_option leanHoG.maxCertificateSize : Nat := {
  defValue := 1024
  descr := "Hard cap, in megabytes, on the LRAT certificate a single solver \
            invocation may write. The solver is killed if it exceeds this. \
            0 disables the cap, which risks filling the disk: an undecidable \
            instance can write tens of GB with no natural stopping point."
}

register_option leanHoG.graphDownloadLocation : String := {
  defValue := "build/graphs"
  descr := "Location for storing downloaded graphs"
}

register_option leanHoG.searchCacheLocation : String := {
  defValue := "build/search_results"
  descr := "Location for caching search results"
}
