# Verifying invariants from HoG

In order to verify the values in HoG, the command `check_hog_graph` has been
added. It takes the graph as an argument.

Example:

```
load_graph Example "file.json"
check_hog_graph Example
```

For an invariant to be verified, the JSON file needs to contain the RawHoG value
for this invariant and the corresponding Lean-HoG certificate.

## Verifying for a set of graphs

A python script was written to generate a lean file containing the code to
verify a set of graphs. This script is called `generateVerifyLean.py` and is
located in the `Verify` directory. It takes as an input a directory containing
JSON files downloaded from HoG and the name of a file where the code should be
written. By default, the input directory is `build/graphs` and the file is
`Verify.lean`. There are some things in place to verify `Verify.lean` more
easily so it is recommended to keep the name.

**Note:** the JSON files must be named in a specific format: <HOG_ID>.json. This
is enforced by the script so that the error messages when verifying those graphs
mentions the id. This is also the default format used when downloading the graph.

### Verifying without opening the lean file

In order to be more practical, a fake lean library named `verify` is defined in
the lakefile.lean that only contains the file `Verify.lean`. This allows the
command below to run and compile the file, therefore verifying the graphs.

`lake build verify`
