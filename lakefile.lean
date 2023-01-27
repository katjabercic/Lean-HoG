import Lake
open Lake DSL

package «lean-HOG» {
  srcDir := "src/hog"
}

lean_lib TreeSet {
}
lean_lib TreeMap

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «LeanHOG» {
  -- add library configuration options here
}
