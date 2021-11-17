from argparse import ArgumentParser
import hog_parser

def main():
    settings = {
        'srcdir': 'data', # Input directory, relative to the project root
        'output_path': 'src/hog/data', # default output directory, relative to project root
        'db_name': 'hog_data_', # prefix for output file names
        'db_main': 'hog_data', # name of the main data Lean module
        'obj_name': 'hog', # objects will be named `obj_name####`
        'raw_hog_type': 'raw_hog', # lean type for the raw graph data
        'raw_hog_namespace': 'hog',# lean namespace for hog data
        'write_floats': False, # ignore fields that contain floating point values
        'graph_id_length': 5, # number of digits needed to represent all graphs
        'graphs_per_file': 1000,
        'graphs_per_line': 10,
        'limit': 3 # if non-zero, output this many graphs
    }

    parser = ArgumentParser()
    parser.add_argument("-o", "--out", dest="output_path",
                        help="output Lean files to this directory")
    args = parser.parse_args()

    # override default output directory if one is passed as an argument
    if args.output_path is not None:
        settings['output_path'] = args.output_path

    hog = hog_parser.HoGParser(settings)

    # hog.write_lean_structure()
    hog.write_lean_files()


if __name__ == "__main__":
    main()