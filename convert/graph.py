# Graphs suitable for conversion from HoG to JSON,
# as well as for computation of certain certificates

import re
import json
from typing import Tuple, List, Set, Dict, Any, AnyStr, Optional, Union
# from connected_components import *
from treeSet import Tree
from treeMap import Map

class Edge():
    fst : int
    snd : int

    def __init__(self, fst : int, snd : int):
        assert (0 <= fst and 0 <= snd and fst != snd)
        self.fst = max(fst, snd)
        self.snd = min(fst, snd)

    def __str__(self) -> str:
        return f'Edge({self.fst},{self.snd})'

    def __repr__(self) -> str:
        return f'Edge({self.fst},{self.snd})'

    def to_json(self):
        return (self.fst, self.snd)

    def __lt__(self, other) -> bool:
        return (self.fst, self.snd) < (other.fst, other.snd)

    def __eq__(self, other) -> bool:
        return (self.fst, self.snd) == (other.fst, other.snd)

    def __hash__(self) -> int:
        return hash((self.fst, self.snd))

def norm_bool(b : str) -> Optional[bool]:
    if b in ['undefined', 'Computation time out', 'Computing']:
        return None
    else:
        assert (b in ['Yes', 'No']), "invalid boolean invariant {0}".format(b)
        return (b == 'Yes')

def norm_nat(k : str) -> Optional[Union[int,float]]:
    if k in ['undefined', 'Computation time out', 'Computing']:
        return None
    elif k == "infinity":
        return float('inf')
    else:
        n = int(k)
        assert (n >= 0), "negative natural number {0}".format(k)
        return n

def norm_float(x : str) -> Optional[float]:
    if x in ['undefined', 'Computation time out', 'Computing']:
        return None
    else:
        if x == 'infinity':
            return float('inf')
        else:
            return float(x)

class Graph():
    """An object representing a single HoG graph"""

    name : str
    vertex_size : int
    edges : Set[Edge]
    invariants : Dict[str, Any] # invariants as loaded from JSON

    # Invariant names in the HoG data, with their declared types
    # NB: The invariants should have the same order as in the input file.
    _invariants = {
        "Acyclic" : norm_bool,
        "Algebraic Connectivity" : norm_float,
        "Average Degree" : norm_float,
        "Bipartite" : norm_bool,
        "Chromatic Index" : norm_nat,
        "Chromatic Number" : norm_nat,
        "Circumference" : norm_nat,
        "Claw-Free" : norm_bool,
        "Clique Number" : norm_nat,
        "Connected" : norm_bool,
        "Density" : norm_float,
        "Diameter" : norm_nat,
        "Edge Connectivity" : norm_nat,
        "Eulerian" : norm_bool,
        "Genus" : norm_nat,
        "Girth" : norm_nat,
        "Hamiltonian" : norm_bool,
        "Independence Number" : norm_nat,
        "Index" : norm_float,
        "Laplacian Largest Eigenvalue" : norm_float,
        "Longest Induced Cycle" : norm_nat,
        "Longest Induced Path" : norm_nat,
        "Matching Number" : norm_nat,
        "Maximum Degree" : norm_nat,
        "Minimum Degree" : norm_nat,
        "Minimum Dominating Set" : norm_nat,
        "Number of Components" : norm_nat,
        "Number of Edges" : norm_nat,
        "Number of Triangles" : norm_nat,
        "Number of Vertices" : norm_nat,
        "Planar" : norm_bool,
        "Radius" : norm_nat,
        "Regular" : norm_bool,
        "Second Largest Eigenvalue" : norm_float,
        "Smallest Eigenvalue" : norm_float,
        "Vertex Connectivity" : norm_nat
    }

    def __init__(self, name : str, txt : str):
        self.name = name
        m = re.fullmatch(r'(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>.*)',
                         txt, flags=re.MULTILINE+re.DOTALL)
        assert m, "invalid hog data:\n{0}".format(txt)
        adjacency = Graph._parse_adjacency(m.group('adjacency'))
        self.vertex_size = len(adjacency)
        # the following will symmetrize the graph in case it isn't already symmetric
        self.edges = set(Edge(u, v) for u in adjacency for v in adjacency[u])
        # store the invariants in a dictionary
        self.invariants = Graph._parse_invariants(m.group('invariants'))
        self._validate_invariants()

    @staticmethod
    def _parse_adjacency(adj_string : str) -> Dict[int, Set[int]]:
        """Return dictionary mapping each vertex to the set of its neighbors."""

        # HoG vertices start at 1
        def normalize(v) -> int:
            w = int(v)
            assert w > 0
            return w-1

        def parse_vertex(m : re.Match[AnyStr]) -> Tuple[int, Set[int]]:
            """Given a match group for a list of neighbors of a vertex, return the vertex and its neighbors"""
            return (normalize(m.group('vertex')), set(normalize(v) for v in m.group('neighbors').split()))

        adjacency : Dict[int, Set[int]]= {}
        for m in re.finditer(r'(?P<vertex>[0-9]+):(?P<neighbors>[0-9 ]*)\n', adj_string):
            (v, nbhs) = parse_vertex(m)
            adjacency[v] = nbhs

        # sanity check: no missing or extraneous vertices or neighbors
        vs : Set[int] = set(adjacency.keys())
        n = len(vs)
        assert vs == set(range(n)), "invalid vertices in an adjancency list"
        assert (all((0 <= w < n and v != w) for v in vs for w in adjacency[v])), "invalid neighbors in an adjacency list"
        return adjacency

    @staticmethod
    def _parse_invariants(txt:str) -> Dict[str, Any]:
        """Convert an iterator of invariant strings into a list of tuples (name, type, value)"""

        invs = {}
        for m in re.finditer(r'(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))', txt):
            name = m.group('invariant')
            assert (name in Graph._invariants), "unknown invariant {0}".format(name)
            normalizer = Graph._invariants[name]
            invs[name] = normalizer(m.group('value'))
        return invs

    def _validate_invariants(self):
        """Validate invariants that can be easily invalidated."""
        assert (self.get_invariant('Number of Edges') == len(self.edges)), "invariant validation: Number of Edgess̄"

    def get_invariant(self, inv):
        return self.invariants[inv]

    def edge_size(self) -> int:
        """Number of edges."""
        return len(self.edges)

    def to_json(self):
        return {
            "vertexSize" : self.vertex_size,
            "edges" : self.edge_tree(),
        }

    def neighbors(self, v):
        """The neighbors of the given vertex."""
        for e in self.edges:
            if e.fst == v: yield e.snd
            elif e.snd == v: yield e.fst

    # def get_data(self):
    #     """Return a dictionary with graph data, to be used in a template file."""

    #     name = self.name.replace("_", "")
    #     return {
    #         'name' : name,
    #         'vertex_size' : self.vertex_size,
    #         'adjacency_list' : self.adjacency_list,
    #         'planar' : self.invariants['Planar']['value'],
    #         'chromatic_number' : self.invariants['Chromatic Number']['value'],
    #         'edge_tree' : self.edge_tree,
    #         'edge_size' : self.edgeSize,
    #         'connected_components_witness' : self.connected_components_witness,
    #         'nbhds_smap' : self.nbhds_smap,
    #         'min_degree' : f'some {self.min_degree}' if self.min_degree is not None else 'none',
    #         'max_degree' : f'some {self.max_degree}' if self.max_degree is not None else 'none',
    #         'is_regular' : str(self.is_regular).lower(),
    #         'is_bipartite' : str(self.is_bipartite).lower()
    #     }

    # def get_invariants(self):
    #     """Return a dictionary with graph invariants (without proofs that they're correct),
    #        to be used in a template file.
    #     """

    #     name = self.name.replace("_", "")
    #     return {
    #         'name' : name,
    #         'vertex_size' : self.vertex_size,
    #         'edge_size' : self.edgeSize,
    #         'min_degree' : f'some {self.min_degree}' if self.min_degree is not None else 'none',
    #         'max_degree' : f'some {self.max_degree}' if self.max_degree is not None else 'none',
    #         'is_regular' : self.is_regular,
    #         'is_bipartite' : self.is_bipartite
    #     }

    def edge_tree(self) -> Tree[Edge]:
        return Tree.from_set(self.edges)

    # def neighborhoods(self):
    #     nbhds = [(i, []) for i in range(self.vertex_size)]
    #     for u, v in self.adjacency_list:
    #         nbhds[u][1].append(v)
    #         nbhds[v][1].append(u)
    #     return nbhds

    # def _neighborhoods_to_smap(self):
    #     def build(nbhds):
    #         n = len(nbhds)
    #         if n == 0:
    #             return None
    #         if n == 1:
    #             vals = Tree.fromList(nbhds[0][1])
    #             return Map(nbhds[0][0], vals, None, None)
    #         else:
    #             mid = n // 2
    #             root_key = nbhds[mid][0]
    #             root_val = Tree.fromList(nbhds[mid][1])
    #             left = build(nbhds[0:mid])
    #             right = build(nbhds[mid+1:])
    #             return Map(root_key, root_val, left, right)

    #     return build(self.neighborhoods())


    # def compute_min_degree(self):
    #     if not self.adjacency_list or len(self.adjacency_list) == 0:
    #         return None
    #     return min([len(nbhd[1]) for nbhd in self.neighborhoods()])

    # def compute_max_degree(self):
    #     if not self.adjacency_list or len(self.adjacency_list) == 0:
    #         return None
    #     return max([len(nbhd[1]) for nbhd in self.neighborhoods()])

    # def compute_bipartiteness(self):
    #     if self.vertex_size == 0 or not self.adjacency_list or len(self.adjacency_list) == 0:
    #         return (False, ([], []))
    #     # Assign a color (0 or 1) to each vertex, starting with None, indicating this vertex is not yet colored
    #     colors = [None for _ in range(self.vertex_size)]
    #     stack = [(0, 0)] # Put the first vertex on the stack, start with color 0
    #     colors[0] = 0 # Color x with the color 0
    #     neighborhoods = self.neighborhoods()
    #     while stack:
    #         x, colorWith = stack.pop() # Pop the next vertex off the stack
    #         if colors[x]: # The vertex has already been colored, this means we have a cycle, we have to check that the colors match
    #             # otherwise we have an odd length cycle
    #             if colors[x] != colorWith:
    #                 return (False, self.colors_to_partition(colors))
    #             else:
    #                 continue
    #         colors[x] = colorWith # Color the current vertex

    #         for neighbor in neighborhoods[x][1]: # Find neighbors of x
    #             if not colors[neighbor]: # This neighbor is not assigned a color yet, put it on the stack
    #                 stack.append((neighbor, (colorWith + 1) % 2)) # Put it on the stack with the next color

    #         if not stack and len(list(filter(lambda x : x == None, colors))) > 0: # There are still uncolored vertices
    #             next_vertex = next(i for i,x in enumerate(colors) if x == None)
    #             stack.append((next_vertex, 0)) # The start color doesn't matter, since this must be a different component

    #     return (True, self.colors_to_partition(colors)) # If we made it to the end of the loop, the graph is bipartite and we get a partition

    # def colors_to_partition(self, colors):
    #     A = []
    #     B = []
    #     for v in range(self.vertex_size):
    #         if colors[v] == 0:
    #             A.append(v)
    #         else:
    #             B.append(v)
    #     return (A, B)
