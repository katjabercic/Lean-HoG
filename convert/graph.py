# Graphs suitable for conversion from HoG to JSON,
# as well as for computation of certain certificates

import re
import json
from typing import Tuple, List
from connected_components import *
from treeSet import Tree
from treeMap import Map
 
class Edge:
    fst : int
    snd : int

    def __init__(self, fst : int, snd : int):
        assert (0 <= fst and 0 <= snd and fst != snd)
        self.fst = max(fst, snd)
        self.snd = min(fst, snd)

    def __str__(self) -> str:
        return f'Edge[{self.fst},{self.snd}]'

    def __lt__(self, other) -> bool:
        return (self.fst, self.snd) < (other.fst, other.snd)

    def __eq__(self, other) -> bool:
        return (self.fst, self.snd) < (other.fst, other.snd)

class Graph:
    """An object representing a single HoG graph"""
    
    vertex_size : int
    adjacency_list : List[Tuple[int, int]]

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

    def __init__(self, name : str, txt : str):
        self.name = name.replace("_", "")
        m = re.fullmatch(r'(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>.*)',
                         txt, flags=re.MULTILINE+re.DOTALL)
        assert m, "Could not parse HoG data:\n{0}".format(txt)
        self.vertex_size, self.adjacency_list = self._get_size_and_adjacency_list(m.group('adjacency'))
        self.invariants = self._get_invariants(m.group('invariants'))
        self.edgeSize = len(self.adjacency_list)
        self.components = compute_components(self.neighborhoods())
        self.connected_components_witness = lean_representation(self.name, self.components[0], self.components[1])
        self.nbhds_smap = self._neighborhoods_to_smap()
        self.min_degree = self.compute_min_degree()
        self.max_degree = self.compute_max_degree()
        self.is_regular = (self.min_degree == self.max_degree)
        self.is_bipartite = self.compute_bipartiteness()[0]
        self.bipartite_witness = self.compute_bipartiteness()[1]

    def _get_size_and_adjacency_list(self, raw_adjacency : str):
        """Return the number of vertices and the list of edges (i, j), such that i < j."""

        # HoG vertices start at 1
        def to_int_minus1(x : int) -> int:
            """Convert a vertex label of type 1--n to one of type 0--(n-1)"""
            assert int(x) > 0
            return int(x) - 1

        def parse_vertex(match) -> List[Tuple[int, int]]:
            """Given a match group for a list of neighbors of a vertex, return a list of edges"""
            vertex = to_int_minus1(match.group('vertex'))
            # sort and filter the neighbors of vertex
            neighbors = sorted(filter(lambda x: vertex < x, map(to_int_minus1, match.group('neighbors').split())))
            return list(map(lambda x: (vertex, x), neighbors))

        adjacency_list : List[Tuple[int,int]]= []
        vertex_size = 0
        for m in re.finditer(r'(?P<vertex>[0-9]+):(?P<neighbors>[0-9 ]*)\n', raw_adjacency):
            vertex_size += 1
            adjacency_list += parse_vertex(m)

        # Sanity checks
        for p in adjacency_list:
            assert p[0] >= 0 and p[1] >= 0

        return vertex_size, adjacency_list

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
            'adjacency_list' : self.adjacency_list,
            'planar' : self.invariants['Planar']['value'],
            'chromatic_number' : self.invariants['Chromatic Number']['value'],
            'edge_tree' : self.edge_tree,
            'edge_size' : self.edgeSize,
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
            'edge_size' : self.edgeSize,
            'min_degree' : f'some {self.min_degree}' if self.min_degree is not None else 'none',
            'max_degree' : f'some {self.max_degree}' if self.max_degree is not None else 'none',
            'is_regular' : self.is_regular,
            'is_bipartite' : self.is_bipartite
        }

    def edge_tree(self) -> Tree[Edge]:
        return Tree.fromList([Edge(*ij) for ij in self.adjacency_list])

    def neighborhoods(self):
        nbhds = [(i, []) for i in range(self.vertex_size)]
        for u, v in self.adjacency_list:
            nbhds[u][1].append(v)
            nbhds[v][1].append(u)
        return nbhds

    def _neighborhoods_to_smap(self):
        def build(nbhds):
            n = len(nbhds)
            if n == 0:
                return None
            if n == 1:
                vals = Tree.fromList(nbhds[0][1])
                return Map(nbhds[0][0], vals, None, None)
            else:
                mid = n // 2
                root_key = nbhds[mid][0]
                root_val = Tree.fromList(nbhds[mid][1])
                left = build(nbhds[0:mid])
                right = build(nbhds[mid+1:])
                return Map(root_key, root_val, left, right)

        return build(self.neighborhoods())


    def compute_min_degree(self):
        if not self.adjacency_list or len(self.adjacency_list) == 0:
            return None
        return min([len(nbhd[1]) for nbhd in self.neighborhoods()])

    def compute_max_degree(self):
        if not self.adjacency_list or len(self.adjacency_list) == 0:
            return None
        return max([len(nbhd[1]) for nbhd in self.neighborhoods()])

    def compute_bipartiteness(self):
        if self.vertex_size == 0 or not self.adjacency_list or len(self.adjacency_list) == 0:
            return (False, ([], []))
        # Assign a color (0 or 1) to each vertex, starting with None, indicating this vertex is not yet colored
        colors = [None for _ in range(self.vertex_size)]
        stack = [(0, 0)] # Put the first vertex on the stack, start with color 0
        colors[0] = 0 # Color x with the color 0
        neighborhoods = self.neighborhoods()
        while stack:
            x, colorWith = stack.pop() # Pop the next vertex off the stack
            if colors[x]: # The vertex has already been colored, this means we have a cycle, we have to check that the colors match
                # otherwise we have an odd length cycle
                if colors[x] != colorWith:
                    return (False, self.colors_to_partition(colors))
                else:
                    continue
            colors[x] = colorWith # Color the current vertex

            for neighbor in neighborhoods[x][1]: # Find neighbors of x
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

class GraphEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, Edge):
            return (obj.fst, obj.snd)
        elif isinstance(obj, Graph):
            lst = [Edge(*e) for e in obj.adjacency_list]
            return {
                "vertexSize" : obj.vertex_size,
                "edges" : obj.edge_tree().to_json()
            }
        else:
            # Let the base class default method raise the TypeError
            return json.JSONEncoder.default(self, obj)
