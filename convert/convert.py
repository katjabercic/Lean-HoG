from argparse import ArgumentParser
import hog_parser

def main():
    settings = {
        'srcdir': 'data', # Input directory, relative to the project root
        'output_path': 'src/hog/data', # default output directory, relative to project root
        'db_name': 'hog_', # prefix for output file names
        'db_main': 'data', # name of the main data Lean module, without the prefix
        'obj_name': 'hog', # objects will be named `obj_name####`
        'write_floats': False, # ignore fields that contain floating point values
        'graph_id_length': 5, # number of digits needed to represent all graphs (used when converting all graphs)
        'graphs_per_file': 50,
        'graphs_per_line': 10,
        # sets the range of graphs to be converted, overrides limit, respects graphs per line/file
        # - None, to get the old behaviour, using limit
        # - skips all graphs from index 0 to start-1
        # - the graph at index end is also converted
        'range': {'start': 1, 'end': 200}
    }

    parser = ArgumentParser()
    parser.add_argument("-o", "--out", dest="output_path",
                        help="output Lean files to this directory")
    parser.add_argument("-l", "--limit", dest="graph_limit", type=int,
                        help="number of graphs to process (0 for all, except for possibly some that get skipped)"
    )
    parser.add_argument("-s", "--skip", dest="skip_graphs", type=int,
                        help="number of graphs to skip (0 for none)"
    )
    args = parser.parse_args()

    # override default output directory if one is passed as an argument
    if args.output_path is not None:
        settings['output_path'] = args.output_path

    if args.skip_graphs is not None:
        settings['range']['start'] = args.skip_graphs + 1

    if args.graph_limit is not None:
        settings['range']['end'] = settings['range']['start'] - 1 + args.graph_limit

    hog = hog_parser.HoGParser(settings)

    # hog.write_lean_structure()
    hog.write_lean_files()


if __name__ == "__main__":
    main()