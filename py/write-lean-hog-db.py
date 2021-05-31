import hogparser

# the invariants should have the same order as in the input file
# in particular, the last invariant is used in parsing as a terminating condition
structure_path = 'py/hog-invariants.json'
input_path = 'etc/order-le-8-inv.txt'
g6_path = 'etc/order-le-8-g6.txt'

hog = hogparser.HoGParser(structure_path)
hog.write_lean_structure()
hog.parse(input_path, g6_path, 'src/hog/db_test.lean')