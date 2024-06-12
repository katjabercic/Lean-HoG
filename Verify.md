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
written. By default, the file is `Verify.lean`. There are some things in place
to verify `Verify.lean` more easily so it is recommended to keep the name.

**Note:** the JSON files must be named in a specific format: <HOG_ID>.json. This
is enforced by the script so that the error messages when verifying those graphs
mentions the id. This is also the default format used when downloading the graph.

### Verifying without opening the lean file

In order to be more practical, a fake lean library named `verify` is defined in
the lakefile.lean that only contains the file `Verify.lean`. This allows the
command below to run and compile the file, therefore verifying the graphs.

`lake build verify`

## Running performance experiments

The python script `verifyBatch.py` is available to perform a verification by
batch. It requires the graphs to be already downloaded in a directory named
`graphs` and the ids of the graphs to verify must be written in a file named
`graphs.txt`. This file allows enforcing some ordering in the verification as
well as ignoring some graphs whose JSON file is present in the directory.

The script takes a batch size as an argument. Should the size be negative,
verification will be performed in reverse order that of the `graphs.txt` file.
An optional argument is a limit or last index. If provided, all graphs will be
verified until this index is reached. For example, a batch size of 10 and a
limit of 22 will verify graphs from 0 to 22 not included. A batch size of -10
and a limit of 22 will verify all graphs from the last one to position 22 but
not graphs in position 0 to 21.

### Analyzing the data

In the directory `timings` are two scripts to help analyze the outputs. The
script `analyze-timings.py` can produce a csv file from the console output of 
`verifyBatch.py` which can then be further analyzed using the functions defined
in `analyze-csv.py`.

A csv file with measurements to verify all the graphs in HoG is provided.
