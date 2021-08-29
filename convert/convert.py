import hog_parser

settings = {
    'srcdir': 'data', # Input directory, relative to the project root
    'output_path': 'src/hog/data', # output directory, relative to project root
    'db_name': 'hog_data_', # prefix for output file names
    'db_main': 'hog_data', # name of the main data Lean module
    'write_floats': False, # ignore fields that contain floating point values
    'total_graphs': 99999, # use for estimating the number of files needed
    'graphs_per_file': 1000,
    'graphs_per_line': 10,
    'limit': 0 # if non-zero, output this many graphs
    # before 2D list, limit: 2690
}

hog = hog_parser.HoGParser(settings)

# hog.write_lean_structure()
hog.write_lean_files()