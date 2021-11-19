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
        'graphs_per_file': 1000,
        'graphs_per_line': 10,
        'limit': 3 # if non-zero, output this many graphs
    }

    parser = ArgumentParser()
    parser.add_argument("-o", "--out", dest="output_path",
                        help="output Lean files to this directory")
    parser.add_argument("-l", "--limit", dest="graph_limit", type=int,
                        help="number of graphs to process (0 for all)"
    )
    args = parser.parse_args()

    # override default output directory if one is passed as an argument
    if args.output_path is not None:
        settings['output_path'] = args.output_path

    if args.graph_limit is not None:
        settings['limit'] = args.graph_limit

    hog = hog_parser.HoGParser(settings)

    # hog.write_lean_structure()
    hog.write_lean_files()


if __name__ == "__main__":
    main()