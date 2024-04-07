import json
from typing import List, Set, Dict, Iterable

class Graph():
    """An object representing a single HoG graph"""
    HoG_id : str
    vertex_size : int
    edges : Set[List[int]]
    adjacency : Dict[int, Set[int]]

    def __init__(self, id : str, data : json):
        self.HoG_id = id
        self.adjacency = Graph._parse_adjacency_list(data['adjacencyList'])
        self.vertex_size = len(self.adjacency)
        self.edges = set(Graph._to_edge(int(u), int(v)) for u in self.adjacency for v in self.adjacency[u])
    
    def vertices(self):
        """An iterator over the vertices of the graph."""
        return range(0, self.vertex_size)

    @staticmethod
    def _to_edge(fst, snd):
        return (min(fst, snd), max(fst, snd))
        
    @staticmethod
    def _parse_adjacency_list(adjList) -> Dict[int, Set[int]]:
        """Return dictionary mapping each vertex to the set of its neighbors."""
        adjacency : Dict[int, Set[int]]= {}
        for (i,nbhd) in enumerate(adjList):
            adjacency[i] = set(nbhd)    
        return adjacency
    
    def neighbors(self, v) -> Iterable[int] :
        """The neighbors of the given vertex."""
        return self.adjacency[v]

    def to_json(self):
        return {
            "vertexSize" : self.vertex_size,
            "edges" : sorted(list(self.edges)),
        }
