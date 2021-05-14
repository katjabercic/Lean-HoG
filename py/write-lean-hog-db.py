import hogparser

# the invariants should have the same order as in the input file
# in particular, the last invariant is used in parsing as a terminating condition
structure_path = 'py/hog-invariants.json'
input_path = 'etc/order-le-6.txt'

hog = hogparser.HoGParser(structure_path)
hog.parse(input_path, 'src/test.lean')