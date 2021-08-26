from os import listdir
from os.path import isfile, join

import hog_parser

# Input directory, relative to the project root
srcdir = 'data'

# Input files
input_files = [
    (f'{srcdir}/hog-order-{x}-inv.txt', f'{srcdir}/hog-order-{x}-g6.txt')
    for x in ['0-8', '9-11', '12-19', '20-21', '22', '23', '24', '25-26', '27', '28', '29',
              '30-regular', '30-nonregular-1', '30-nonregular-2',
              '31-33', '34', '35-41', '42-43', '44-49', '50-99',
              '100-149', '150-189', '190-209', '210-']
  ]

settings = {
    'inputs': input_files,
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
