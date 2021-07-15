import hogparser

# the invariants should have the same order as in the input file
# in particular, the last invariant is used in parsing as a terminating condition

files = ['0-8', '9-11', '12-19']

settings = {
    'structure_path': 'py/hog-invariants.json',
    'inputs': list(map(lambda x: (f'etc/hog-order-{x}-inv.txt', f'etc/hog-order-{x}-g6.txt'), files)),
    'output_path': 'src/hog/db_test.lean',
    'write_floats': False,
    'limit': 2690
}
hog = hogparser.HoGParser(settings)
hog.write_lean_structure()
hog.parse(10)