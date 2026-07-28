import Lean

open Lean Elab Term

/--
Expands to the absolute path of the Lean-HoG package root, resolved while
*this file* is being elaborated put in the `.olean` as a string literal.

The three `.parent` climbs assume this file lives at
`<root>/LeanHoG/Util/PackageDir.lean`. Moving it changes the expansion;
adjust the number of climbs if you move it.
-/
elab "leanHoG_dir%" : term => do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some d1 := srcPath.parent | throwError "cannot compute parent directory of `{srcPath}`"
  let some d2 := d1.parent | throwError "expected `{d1}` inside `LeanHoG/Util`"
  let some root := d2.parent | throwError "expected `{d2}` to sit inside the LeanHoG package root"
  return mkStrLit root.toString

/-- Absolute path of the Lean-HoG package root, fixed when Lean-HoG itself was
compiled. Use this to locate files shipped with the package, such as the Python
scripts under `Download/`. -/
def packageDir : String := leanHoG_dir%
