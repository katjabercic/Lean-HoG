# Main program

from typing import Tuple, List, Optional
import os
import os.path
import pathlib
import re
import logging
import json
from string import Template
from argparse import ArgumentParser

from graph import GraphEncoder, Graph

def hog_generator(datadir, prefix:str, skip=0, limit=None):
    """Generate HoG graphs from input files datadir, skipping the first
       skip files, and generating at most limit graphs."""

    if skip > 0: logging.info (f"skipping {skip} graphs")    
    if limit is not None: logging.info (f"limitting to {limit} graphs")    
    files = sorted(f for f in os.listdir(datadir) if f.endswith('.txt'))
    if len(files) == 0:
        logging.warning("no data files found (hint: git submodule init && git submodule update)")
    k = 0 # serial number
    for fh in files:
        # Process next file
        with open(os.path.join(datadir, fh), 'r') as fh:
            # Iterate through all graphs in the file
            for txt in re.finditer(r'^1:.+?^Vertex Connectivity: .+?\n', fh.read(), flags=re.DOTALL+re.MULTILINE):
                k += 1
                if k < skip:
                    logging.debug (f"skipping graph {k}")
                    continue
                elif limit is not None and k >= skip + limit:
                    logging.debug (f"limit reached at graph {k}")
                    return
                else:
                    logging.debug (f"processing graph {k}")
                    yield Graph("{0}{1:05d}".format(prefix, k), txt.group(0))
        
def write_json_files(datadir, outdirData, prefix, skip : int = 0, limit : Optional[int] = None):
    """Convert HoG graphs in the datadir to JSON and save them to destdir.
       If the limit is given, stop afer that many graphs.
       The generated filenames have the form prefixXXXXX.json where XXXXX is the serial number.
       """

    # # Load the template file
    # with open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_graph.txt')) as fh, open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_connected_components.txt')) as fh_cc, open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_invariants.txt')) as fh_inv:
    #     template = Template(fh.read())
    #     templace_cc = Template(fh_cc.read())
    #     template_invariants = Template(fh_inv.read())

    # Make sure the output directory exists
    if os.path.exists(outdirData):
        assert os.path.isdir(outdirData), "{0} exists but is not a directory".format(outdirData)
    else:
        pathlib.Path(outdirData).mkdir(parents=True, exist_ok=True)
        logging.info("created output folder {0}".format(outdirData))

    # with open(os.path.join(outdirData, "Invariants.lean"), 'a') as fh:
    #     fh.write("import Query\n\nnamespace Hog\n")

    names = []
    counter = 1 # the first graph has serial number 1
    for graph in hog_generator(datadir, prefix=prefix, skip=skip, limit=limit):
        names.append(graph.name)
        with open(os.path.join(outdirData, "{0}.json".format(graph.name)), 'w') as fh:
            json.dump(graph, fh, cls=GraphEncoder)
        counter += 1

    logging.info ("wrote {0} graphs to {1}".format(counter, outdirData))


########################################################
### MAIN PROGRAM

if __name__ == "__main__":
    mydir = os.path.abspath(os.path.dirname(__file__))

    def relative(*fs):
        """The location of a file, relative to this file."""
        return os.path.join(mydir, *fs)

    arg_parser = ArgumentParser()
    arg_parser.add_argument("--srcdir", dest="datadir", required=True,
                        help="read HoG graph files from this directory")
    arg_parser.add_argument("--destdir", default=relative('..', 'src', 'hog', 'data', 'Data'), dest="outdirData",
                        help="output JSON graph files to this directory")
    arg_parser.add_argument("--limit", type=int, default=None, dest="limit",
                        help="limit the number of graphs to process")
    arg_parser.add_argument("--skip", type=int, default=0, dest="skip",
                        help="skip this many graphs initially")
    arg_parser.add_argument("--loglevel", type=int, default=30, dest="loglevel",
                        help="set logging level (0 to 50)")
    args = arg_parser.parse_args()

    # set logging level
    logging.getLogger().setLevel(args.loglevel)
    # hog.write_lean_structure()
    write_json_files(
        datadir=args.datadir,
        outdirData=args.outdirData,
        prefix='hog',
        limit=args.limit,
        skip=args.skip
    )
