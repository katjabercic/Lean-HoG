import typing
import os
import sys
import argparse

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

def validEntry(entry : os.DirEntry) -> type[str | None]:
    """
    Check that we have a format {numbers}.json. Returns the commands as a string if it is the case and None otherwise.
    """
    if entry.is_file() and entry.name.endswith(".json") and entry.name[:-5].isnumeric():
        hogId = int(entry.name[:-5])
        return GRAPH_CHECK_COMMANDS.format(id=hogId, path=entry.path)
    else:
        return None

def main(inputDirName : str, outputFile: str):
    """
    Scans the given directory and, for every HoG graph json, writes the commands to the given output file.
    """
    with os.scandir(inputDirName) as iterator, open(outputFile, "w") as outputWriter:
       outputWriter.write(FILE_INIT)
       for entry in filter(lambda x : x is not None, map(validEntry, iterator)):
           outputWriter.write(entry)
           outputWriter.write("\n")

def parse_arguments():
    """
    Parses console arguments
    """
    parser = argparse.ArgumentParser(
        prog="verifyBatch",
        description="""\
Generate a lean file containing the commands to verify the HoG invariants for
the given HoG graphs in json format. If giving an output file, an input
directory *must* be provided.
"""
    )
    parser.add_argument(
        "inputDir",
        type=str,
        help="""The name of an input directory containing HoG graphs in JSON format.
            Their name should be of the form <numbers>.json."""
    )
    parser.add_argument(
        "-o", "--output",
        type=str,
        help="""
        The name of the lean file to create. Default: Verify.lean
        """,
        default="Verify.lean"
    )
    args = parser.parse_args()
    return args

if __name__ == '__main__':
    args = parse_arguments()
    main(args.inputDir, args.output)
