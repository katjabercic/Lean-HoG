import typing
import os
import sys
import subprocess
import argparse

# Imports
FILE_INIT = """\
import LeanHoG.LoadGraph

namespace LeanHoG

"""

# What should be done for each graphs
GRAPH_CHECK_COMMANDS = """\
section sec_hog_{id}
    load_graph hog_{id} \"{path}\"
    check_hog_graph hog_{id}
end sec_hog_{id}
"""

def get_default(array, index, default):
    """
    Returns the element at index in the array or a default value
    """
    if index < len(array):
        return array[index]
    else:
        return default

def generateBatch(inputDirName : str, outputFile: str, ids, start: int, stop: int, reverse: bool):
   """
   Writes the commands to verify the graphs with index between start and stop in the ids list.
   If reverse, starts writing them in reverse order.
   The json files corresponding to the graphs must be present in inputDirName.
   """
   increment = 1 if not reverse else -1
   with open(outputFile, "w") as outputWriter:
       outputWriter.write(FILE_INIT)
       index = start
       while 0 <= index < len(ids) and index != stop:
           id = ids[index]
           entry = GRAPH_CHECK_COMMANDS.format(id=id, path=os.path.join(inputDirName, f"{id}.json"))
           outputWriter.write(entry)
           outputWriter.write("\n")
           index += increment

def get_ids(listFile):
    """
    Returns the list of ids contained in the given file.
    """
    with open(listFile) as lst:
        ids = map(lambda x : int(x.strip()), lst.readlines())
        return list(ids)

def handleBatch(inputDirName, outputFile, ids, start, stop, reverse):
    """
    Verifies the graphs whose ids are in ids at index between start and stop.
    """
    print(f"Doing ids {start} to {stop}.")
    print("    Generating lean file.")
    generateBatch(inputDirName, outputFile, ids, start, stop, reverse)
    print("    Verifying.")
    subprocess.run(["/usr/bin/time", "--format", "Time %E CPU: User %U Kernel %S Average mem %K Max mem %M", "lake", "build", "verify"])
    print(f"Done ids {start} to {stop}.")

def loopCond(start, stop, length, limit, reverse):
    """
    Condition to know when we reached the end of the list of ids
    """
    if not reverse:
        return start < length and start < limit
    else:
        return start >= 0 and start > limit

def limitedEnd(stop, limit, reverse):
    """
    The last index we should verify between stop, the normal last index and limit, a user-provided parameter.
    """
    if not reverse:
        return min(stop, limit)
    else:
        return max(stop, limit)

def parse_arguments():
    """
    Parses console arguments
    """
    parser = argparse.ArgumentParser(
        prog="verifyBatch",
        description="""
Verifies graph invariants. In order to work, it requires a file named graphs.txt
containing on each line a HoG id. For each id, a json file containing the data
must be present in a directory named graphs. The filename must be <id>.json.
"""
    )
    parser.add_argument(
        "batchSize",
        type=int,
        help="Size of batches. Negative values means reverse order."
    )
    parser.add_argument(
        "-l", "--limit",
        type=int,
        help="Last index in the ids list to check. If reverse order, all the graphs after it will be checked."
    )
    args = parser.parse_args()
    if args.batchSize == 0:
        raise argparse.ArgumentTypeError("batchSize must not be zero.")
    return args

def main():
    args = parse_arguments()
    ids = get_ids("graphs.txt")
    reverse = args.batchSize < 0
    if args.limit is None:
        args.limit = len(ids) if not reverse else -1
    start = 0 if not reverse else len(ids) - 1
    end = start + args.batchSize
    while loopCond(start, end, len(ids), args.limit, reverse):
        handleBatch("graphs", "Verify.lean", ids, start, limitedEnd(end, args.limit, reverse), args.batchSize)
        start = end
        end = start + args.batchSize

if __name__ == "__main__":
    main()
