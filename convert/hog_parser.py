import graphlib
import re
import os
from string import Template

class HoGGraph:
    """An object representing a single HoG graph"""

    # Invariant names in the HoG data, with their declared types
    # NB: The invariants should have the same order as in the input file.
    _structure = {
        "Acyclic": "bool",
        "Algebraic Connectivity": "float",
        "Average Degree": "float",
        "Bipartite": "bool",
        "Chromatic Index": "int",
        "Chromatic Number": "int",
        "Circumference": "int",
        "Claw-Free": "bool",
        "Clique Number": "int",
        "Connected": "bool",
        "Density": "float",
        "Diameter": "int",
        "Edge Connectivity": "int",
        "Eulerian": "bool",
        "Genus": "int",
        "Girth": "int",
        "Hamiltonian": "bool",
        "Independence Number": "int",
        "Index": "float",
        "Laplacian Largest Eigenvalue": "float",
        "Longest Induced Cycle": "int",
        "Longest Induced Path": "int",
        "Matching Number": "int",
        "Maximum Degree": "int",
        "Minimum Degree": "int",
        "Minimum Dominating Set": "int",
        "Number of Components": "int",
        "Number of Edges": "int",
        "Number of Triangles": "int",
        "Number of Vertices": "int",
        "Planar": "bool",
        "Radius": "int",
        "Regular": "bool",
        "Second Largest Eigenvalue": "float",
        "Smallest Eigenvalue": "float",
        "Vertex Connectivity": "int"
    }

    def __init__(self, name, txt):
        self.name = name
        graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
        m = graph_pattern.search(txt)
        if not m:
            raise ValueError
        else:
            self.vertex_size, self.edge_list = self._get_size_edge_list(m.group('adjacency'))
            self.invariants = self._get_invariants(m.group('invariants'))
                
    def _get_size_edge_list(self, raw_adjacency):
        """Return the number of vertices and the list of edges (i, j), such that i < j."""

        # HoG vertices start at 1
        def to_int_minus1(x):
            """Convert a vertex label of type 1--n to one of type 0--(n-1)"""
            assert int(x) > 0
            return int(x) - 1

        def parse_vertex(match):
            """Given a match group for a list of neighbors of a vertex, return a list of edges"""
            vertex = to_int_minus1(match.group('vertex'))
            # sort and filter the neighbors of vertex
            neighbors = sorted(filter(lambda x: vertex < x, map(to_int_minus1, match.group('neighbors').split())))
            return list(map(lambda x: (vertex, x), neighbors))

        edge_list = []
        vertex_size = 0
        for m in re.finditer(r'(?P<vertex>[0-9]+):(?P<neighbors>[0-9 ]*)\n', raw_adjacency):
            vertex_size += 1
            edge_list += parse_vertex(m)

        # Sanity checks
        for p in edge_list:
            assert p[0] >= 0 and p[1] >= 0
 
        return vertex_size, edge_list

    def _get_invariants(self, invariants):
        """Convert an iterator of invariant strings into a list of tuples (name, type, value)"""

        def checked_invariant_value(inv_type, val_str):
            """Validate and convert a string to given value type."""
            value = None
            if val_str in ['undefined', 'Computation time out', 'Computing']:
                value = None
            else:
                if inv_type == 'bool':
                    if val_str in ['Yes', 'No']: # valid bool values
                        value = val_str == 'Yes'
                    else:
                        raise ValueError # fail early
                elif val_str == 'infinity': # for now, ok for ints and floats
                    value = 'infinity'
                elif inv_type == 'int':
                    value = int(val_str)
                elif inv_type == 'float':
                    value = float(val_str)
                else:
                    raise ValueError # fail early
            return value

        inv_list = {}
        invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')
        for m in invariant_pattern.finditer(invariants):
            name = m.group('invariant')
            inv_type = self._structure[name]
            value = checked_invariant_value(inv_type, m.group('value'))
            inv_list[name] = { 'type': inv_type, 'value': value }
        return inv_list

def get_data(self):
    """Return a dictionary with graph data, to be used in a template file."""

    return {
        'name' : self.name,
        'vertex_size' : self._vertex_size,
        'edge_list' : self._edge_list,
        'planar' : self.invariants['Planar']['value'],
        'chromatic_number' : self.invariants['Chromatic Number']['value'],
    }


def hog_generator(datadir, file_prefix, limit=None):
    """Generate HoG graphs from input files in the given data directory.
       Stop if the limit is given and reached."""

    counter = 1

    # Iterate through all the .txt files in the data directory
    for input_file in sorted(f for f in os.listdir(datadir) if f.endswith('.txt')):
        # Process next file
        with open(input_file, 'r') as fh:
            # Iterate through all graphs in the file
            for txt in re.finditer(r'^1: .+?^Vertex Connectivity: .+?$', txt, flags=re.DOTALL+re.MULTILINE):
                if limit is None or counter < limit:
                    yield HoGGraph("{0}{1:05d}".format(file_prefix, counter), txt)
                    counter += 1
                else:
                    # Stop if the limit is reached
                    return


def write_lean_files(datadir, destdir, file_prefix, limit=None):
    """Convert HoG graphs in the datadir to Lean code and save them to destdir.
       If the limit is given, stop afer that many graphs.
       Use the file_prefix to generate the Lean output filename.
       """

    # Load the template file
    with open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_graph.txt')) as fh:
        template = Template(fh.read())

    # Make sure the output directory exists
    if os.path.exists(destdir):
        assert os.path.isdir(destdir), "{0} exists but is not a directory".format(destdir)
    else:
        os.mkdir(destdir)

    for graph in hog_generator(datadir, limit=limit, file_prefix=file_prefix):
        with open(os.path.join(destdir, "{0}.lean".format(graph.name)), 'w') as fh:
            fh.write(template.substitute(graph.get_data()))
