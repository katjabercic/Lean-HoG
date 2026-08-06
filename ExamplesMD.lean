import Mdgen.File
import Mdgen.ConvertToMd

def main (argv : List String) : IO UInt32 := do
  let fname := argv[0]!;
  let oname := argv[1]!;
  let fcontents ← IO.FS.lines fname;
  let mdcontents := convertToMd none none fcontents;
  IO.FS.writeFile oname mdcontents;
  return 0
