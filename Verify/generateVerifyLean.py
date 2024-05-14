import typing
import os
import sys

USAGE = """\
generateVerifyLean.py [input] [output]

Generate a lean file containing the commands to verify the HoG invariants for
the given HoG graphs in json format. If giving an output file, an input
directory *must* be provided.

parameters:
    input   The name of an input directory containing HoG graphs in JSON format.
            Their name should be of the form <numbers>.json. Default: build/graphs

    output  The name of the lean file to create. Default: Verify.lean
"""

# Imports
FILE_INIT = """\
import LeanHoG.LoadGraph

namespace LeanHoG

"""

# What should be done for each graphs
GRAPH_CHECK_COMMANDS = """\
load_graph hog_{id} \"{path}\"
check_hog_graph hog_{id}
"""

# Check that we have a format {numbers}.json. Returns the commands as a string if it is the case and None otherwise.
def validEntry(entry : os.DirEntry) -> type[str | None]:
    if entry.is_file() and entry.name.endswith(".json") and entry.name[:-5].isnumeric():
        hogId = int(entry.name[:-5])
        return GRAPH_CHECK_COMMANDS.format(id=hogId, path=entry.path)
    else:
        return None

# Scans the given directory and, for every HoG graph json, writes the commands to the given output file.
def main(inputDirName : str, outputFile: str):
   with os.scandir(inputDirName) as iterator, open(outputFile, "w") as outputWriter:
       outputWriter.write(FILE_INIT)
       for entry in filter(lambda x : x is not None, map(validEntry, iterator)):
           outputWriter.write(entry)
           outputWriter.write("\n")

if __name__ == '__main__':
    args = sys.argv
    inputDir = "build/graphs"
    outputFile = "Verify.lean"
    if len(args) > 1:
        inputDir = args[1]
    if len(args) == 3:
        outputFile = args[2]
    try:
        if 1 <= len(args) < 4:
                main(inputDir, outputFile)
        else:
            print("Too many arguments.\n")
            print(USAGE)
            sys.exit(1)
    except Exception as e:
        print(e)
        print()
        print(USAGE)
        sys.exit(1)
