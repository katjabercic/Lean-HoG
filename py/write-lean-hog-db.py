from os import listdir
from os.path import isfile, join

import hogparser


# the invariants should have the same order as in the input file
# in particular, the last invariant is used in parsing as a terminating condition

files = ['0-8', '9-11', '12-19', '20-21', '22', '23', '24', '25-26', '27', '28', '29']
        # 
         # , '30-regular', '30-nonregular-1', '30-nonregular-2'

settings = {
    'structure_path': 'py/hog-invariants.json',
    'inputs': list(map(lambda x: (f'etc/hog-order-{x}-inv.txt', f'etc/hog-order-{x}-g6.txt'), files)),
    'output_path': 'src/hog/db_test.lean',
    'write_floats': False,
    'limit': 0
    # before 2D list, limit: 2690
}

hog = hogparser.HoGParser(settings)
hog.write_lean_structure()
hog.parse(10)