import os
import os.path
import pathlib
import re
from string import Template
from argparse import ArgumentParser
import math

from connected_components import compute_components, h_representation, connect_edges_representation, root_representation, is_root_representation, uniqueness_of_roots_representation, next_representation, height_cond_representation, lean_representation

class Edge:
    def __init__(self, val):
        self.val = val

    def __str__(self):
        return f'(Edge.mk {str(self.val)})'

class Stree:
    def __init__(self, val, left, right):
        """Stree(None, _, _) creates an empty tree.
           Stree(v, l, r) creates a non-empty tree.
           We optimize subtrees by setting left and right to None instead of an empty tree."""
        self.val = val
        self.left = None if val is None or (left is None) or left.is_empty() else left
        self.right = None if val is None or (right is None) or right.is_empty() else right

    def is_empty(self):
        return (self.val is None)

    def has_left(self):
        return not self.is_empty() and self.left is not None

    def has_right(self):
        return not self.is_empty() and self.right is not None

    def is_leaf(self):
        return not self.is_empty() and not self.has_left() and not self.has_right()

    def __str__(self):
        if self.is_empty():
            return "Stree.empty (by first | bool_reflect | rfl)"
        elif self.is_leaf():
            return "Stree.leaf " + str(self.val) + " (by first | bool_reflect | rfl) (by first | bool_reflect | rfl)"
        else:
            if self.has_left():
                left = str(self.left)
            else:
                left = "Stree.empty (by first | bool_reflect | rfl)"
            if self.has_right():
                right = str(self.right)
            else:
                right = "Stree.empty (by first | bool_reflect | rfl)"
            return "Stree.node " + str(self.val) + "\n(" + left + ")\n(" + right + ")"

class Smap:
    def __init__(self, key, val, left, right):
        self.key = key
        self.val = val
        self.left = left
        self.right = right

    def __str__(self):
        if self.val is None:
            return "Smap.empty (by first | bool_reflect | rfl)"
        if self.left is None and self.right is None:
            return "Smap.leaf " + str(self.key) + " (" + str(self.val) + ") " + " (by first | bool_reflect | rfl) (by first | bool_reflect | rfl)"
        if self.left is None:
            left = "Smap.empty (by first | bool_reflect | rfl)"
        else:
            left = str(self.left)
        if self.right is None:
            right = "Smap.empty (by first | bool_reflect | rfl)"
        else:
            right = str(self.right)
        return "Smap.node " + str(self.key) + " (" + str(self.val) + ") " + "\n(" + left + ")\n(" + right + ")"
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
        self.name = name.replace("_", "")
        m = re.fullmatch(r'(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>.*)',
                         txt, flags=re.MULTILINE+re.DOTALL)
        assert m, "Could not parse HoG data:\n{0}".format(txt)
        self.vertex_size, self.edge_list = self._get_size_edge_list(m.group('adjacency'))
        self.invariants = self._get_invariants(m.group('invariants'))
        self.stree = self.edge_list_to_stree(self.edge_list)
        self.edge_size = len(self.edge_list)
        self.neighborhoods = self.edge_list_to_neighborhoods(self.edge_list)
        self.components = compute_components(self.neighborhoods)
        self.connected_components_witness = lean_representation(self.name, self.components[0], self.components[1])
        self.nbhds_smap = self.neighborhoods_to_smap(self.neighborhoods)
        self.min_degree = self.compute_min_degree()
        self.max_degree = self.compute_max_degree()
        self.is_regular = (self.min_degree == self.max_degree)
        self.is_bipartite = self.compute_bipartiteness()[0]
        self.bipartite_witness = self.compute_bipartiteness()[1]
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

    def _get_invariants(self, txt):
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
        for m in re.finditer(r'(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))', txt):
            name = m.group('invariant')
            inv_type = self._structure[name]
            value = checked_invariant_value(inv_type, m.group('value'))
            inv_list[name] = { 'type': inv_type, 'value': value }
        return inv_list

    def get_data(self):
        """Return a dictionary with graph data, to be used in a template file."""

        name = self.name.replace("_", "")
        return {
            'name' : name,
            'vertex_size' : self.vertex_size,
            'edge_list' : self.edge_list,
            'planar' : self.invariants['Planar']['value'],
            'chromatic_number' : self.invariants['Chromatic Number']['value'],
            'stree' : self.stree,
            'edge_size' : self.edge_size,
            'connected_components_witness' : self.connected_components_witness,
            'nbhds_smap' : self.nbhds_smap,
            'min_degree' : f'some {self.min_degree}' if self.min_degree is not None else 'none',
            'max_degree' : f'some {self.max_degree}' if self.max_degree is not None else 'none',
            'is_regular' : str(self.is_regular).lower(),
            'is_bipartite' : str(self.is_bipartite).lower()
        }

    def get_invariants(self):
        """Return a dictionary with graph invariants (without proofs that they're correct),
           to be used in a template file.
        """

        name = self.name.replace("_", "")
        return {
            'name' : name,
            'vertex_size' : self.vertex_size,
            'edge_size' : self.edge_size,
            'min_degree' : f'some {self.min_degree}' if self.min_degree is not None else 'none',
            'max_degree' : f'some {self.max_degree}' if self.max_degree is not None else 'none',
            'is_regular' : self.is_regular,
            'is_bipartite' : self.is_bipartite
        }

    def edge_list_to_stree(self, edge_list):
        n = len(edge_list)
        if n == 0:
            return Stree(None, None, None)
        mid = n // 2
        root = Edge(edge_list[mid])
        left = self.edge_list_to_stree(edge_list[0:mid])
        right = self.edge_list_to_stree(edge_list[mid+1:])
        return Stree(root, left, right)

    def list_to_stree(self, l):
        n = len(l)
        if n == 0:
            return Stree(None, None, None)
        mid = n // 2
        root = l[mid]
        left = self.list_to_stree(l[0:mid])
        right = self.list_to_stree(l[mid+1:])
        total = Stree(root, left, right)
        return total

    def edge_list_to_neighborhoods(self, edge_list):
        if not self.vertex_size:
            raise RuntimeError("You have to compute vertex_size before computing neighborhoods!")
        nbhds = [(i, []) for i in range(self.vertex_size)]
        for u, v in edge_list:
            nbhds[u][1].append(v)
            nbhds[v][1].append(u)
        return nbhds

    def neighborhoods_to_smap(self, nbhds):
        if not self.vertex_size:
            raise RuntimeError("You have to compute vertex_size before computing neighborhoods!")
        n = len(nbhds)
        if n == 0:
            return None
        if n == 1:
            vals = self.list_to_stree(nbhds[0][1])
            return Smap(nbhds[0][0], vals, None, None)
        mid = n // 2
        root_key = nbhds[mid][0]
        root_val = self.list_to_stree(nbhds[mid][1])
        left = self.neighborhoods_to_smap(nbhds[0:mid])
        right = self.neighborhoods_to_smap(nbhds[mid+1:])
        return Smap(root_key, root_val, left, right)

    def compute_min_degree(self):
        if not self.edge_list or len(self.edge_list) == 0:
            return None
        return min([len(nbhd[1]) for nbhd in self.neighborhoods])

    def compute_max_degree(self):
        if not self.edge_list or len(self.edge_list) == 0:
            return None
        return max([len(nbhd[1]) for nbhd in self.neighborhoods])

    def compute_bipartiteness(self):
        if self.vertex_size == 0 or not self.edge_list or len(self.edge_list) == 0:
            return (False, ([], []))
        # Assign a color (0 or 1) to each vertex, starting with None, indicating this vertex is not yet colored
        colors = [None for _ in range(self.vertex_size)]
        stack = [(0, 0)] # Put the first vertex on the stack, start with color 0
        colors[0] = 0 # Color x with the color 0
        while stack:
            x, colorWith = stack.pop() # Pop the next vertex off the stack
            if colors[x]: # The vertex has already been colored, this means we have a cycle, we have to check that the colors match
                # otherwise we have an odd length cycle
                if colors[x] != colorWith:
                    return (False, self.colors_to_partition(colors))
                else:
                    continue
            colors[x] = colorWith # Color the current vertex

            for neighbor in self.neighborhoods[x][1]: # Find neighbors of x
                if not colors[neighbor]: # This neighbor is not assigned a color yet, put it on the stack
                    stack.append((neighbor, (colorWith + 1) % 2)) # Put it on the stack with the next color

            if not stack and len(list(filter(lambda x : x == None, colors))) > 0: # There are still uncolored vertices
                next_vertex = next(i for i,x in enumerate(colors) if x == None)
                stack.append((next_vertex, 0)) # The start color doesn't matter, since this must be a different component

        return (True, self.colors_to_partition(colors)) # If we made it to the end of the loop, the graph is bipartite and we get a partition

    def colors_to_partition(self, colors):
        A = []
        B = []
        for v in range(self.vertex_size):
            if colors[v] == 0:
                A.append(v)
            else:
                B.append(v)
        return (A, B)


def hog_generator(datadir, file_prefix):
    """Generate HoG graphs from input files in the given data directory.
       Stop if the limit is given and reached."""

    counter = 1

    # Iterate through all the .txt files in the data directory
    for input_file in sorted(f for f in os.listdir(datadir) if f.endswith('.txt')):
        # Process next file
        with open(os.path.join(datadir, input_file), 'r') as fh:
            # Iterate through all graphs in the file
            for txt in re.finditer(r'^1:.+?^Vertex Connectivity: .+?\n', fh.read(), flags=re.DOTALL+re.MULTILINE):
                yield HoGGraph("hog{0:05d}".format(counter), txt.group(0))
                counter += 1


def write_lean_files(datadir, outdirData, file_prefix, limit=None, skip=0):
    """Convert HoG graphs in the datadir to Lean code and save them to destdir.
       If the limit is given, stop afer that many graphs.
       Use the file_prefix to generate the Lean output filename.
       """

    # Load the template file
    with open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_graph.txt')) as fh, open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_connected_components.txt')) as fh_cc, open(os.path.join(os.path.abspath(os.path.dirname(__file__)), 'template_invariants.txt')) as fh_inv:
        template = Template(fh.read())
        templace_cc = Template(fh_cc.read())
        template_invariants = Template(fh_inv.read())

    # Make sure the output directory exists
    if os.path.exists(outdirData):
        assert os.path.isdir(outdirData), "{0} exists but is not a directory".format(outdirData)
    else:
        print ("Creating {0}".format(outdirData))
        pathlib.Path(outdirData).mkdir(parents=True, exist_ok=True)

    with open(os.path.join(outdirData, "Invariants.lean"), 'a') as fh:
        fh.write("import Query\n\nnamespace Hog\n")

    counter = 0
    names = []
    for graph in hog_generator(datadir, file_prefix=file_prefix):
        if limit is not None and counter >= skip + limit:
            print ("We reached the limit of {0} graphs, skipping the rest.".format(limit))
            break
        names.append(graph.name)
        if counter < skip:
            print ("Skipping graph {0}".format(graph.name), end='\r')
        else:
            print ("Writing graph {0}".format(graph.name), end='\r')
            with open(os.path.join(outdirData, "{0}.lean".format(graph.name)), 'w') as fh:
                fh.write(template.substitute(graph.get_data()))
            with open(os.path.join(outdirData, "components_{0}.lean".format(graph.name)), 'w') as fh:
                fh.write(templace_cc.substitute(graph.get_data()))
            with open(os.path.join(outdirData, "Invariants.lean"), 'a') as fh:
                fh.write(template_invariants.substitute(graph.get_invariants()))

        counter += 1

    with open(os.path.join(outdirData, "Invariants.lean"), 'a') as fh:
        fh.write("\ndef invariants : List GraphInvariants := [")
        for i, name in enumerate(names):
            fh.write(name + "_invariants")
            if i < len(names) - 1:
                fh.write(",")
            else:
                fh.write("]")
        fh.write("\n\nend Hog")

    print ("Wrote {0} graphs to {1}".format(counter - skip, outdirData))


########################################################
### MAIN PROGRAM

if __name__ == "__main__":
    mydir = os.path.abspath(os.path.dirname(__file__))

    def relative(*fs):
        """The location of a file, relative to this file."""
        return os.path.join(mydir, *fs)

    arg_parser = ArgumentParser()
    arg_parser.add_argument("--datadir", dest="datadir",
                        help="read HoG graph files from this directory")
    arg_parser.add_argument("--outdirData", default=relative('..', 'src', 'hog', 'data', 'Data'), dest="outdirData",
                        help="output Lean graph files to this directory")
    arg_parser.add_argument("--limit", type=int, default=0, dest="limit",
                        help="limit the number of graphs to process")
    arg_parser.add_argument("--skip", type=int, required=False, dest="skip",
                        help="skip this many graphs initially")
    args = arg_parser.parse_args()

    # hog.write_lean_structure()
    write_lean_files(
        datadir=args.datadir,
        outdirData=args.outdirData,
        file_prefix='Hog',
        limit=args.limit,
        skip=args.skip
    )
