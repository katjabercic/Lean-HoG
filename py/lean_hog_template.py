import re

graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
adjacency_pattern = re.compile('(?P<vertex>[0-9])+:(?P<neighbors>[0-9 ]*)\n')
invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')

def _graph_name(num):
    return 'hog' + str(num).zfill(4)

# Prints a list of graph names from 1 to n-1
def _names_list(n, per_line):
    if n < 1:
        return ''
    r = _graph_name(1)
    for i in range(2, n):
        br = '\n' if ((i-1) % per_line) == 0 else ' '
        r += ',' + br + _graph_name(i)
    return r

def _graph_from_preadjacency(num, preadjacency):
    return f'def {_graph_name(num)} : preadjacency := from_adjacency_list {str(preadjacency)}'

def convert_invariant_name(name):
    return (name.lower()).replace(' ', '_').replace('-', '_')

# just prints out default for floats
def lean_property(name, value):
    n = convert_invariant_name(name)
    v = f'some ({value})'
    if value is True:
        v = 'some tt'
    elif value is False:
        v = 'some ff'
    elif value is None or value == 'infinity':
        v = 'none'
    return f'  {n} := {v}'

def get_graph_boilerplate(position, g6):
    g6_lean = g6.strip().replace('\\', '\\\\')
    begin = (
        f'def {_graph_name(position)} := {{ hog .\n'
        f'  graph6 := "{g6_lean}",\n'
    )
    if position != 1:
        begin = '\n' + begin
    end = '\n}'
    return begin, end

def get_db_preamble():
    return 'import .hog\n\nnamespace hog\n\n'

def get_db_epilog(num_graphs, per_line):
    return '\n\ndef database := [\n' + _names_list(num_graphs, per_line) + '\n]\n\nend hog'