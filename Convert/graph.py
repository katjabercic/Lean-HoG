import json
from typing import List, Set, Dict, Any

class Graph():
    """An object representing a single HoG graph"""
    HoG_id : int
    vertex_size : int
    edges : Set[List[int]]
    hamiltonianPath : List[int]

    def __init__(self, id : str, data : json):
        self.HoG_id = int(id)
        adjacency = Graph._parse_adjacency_list(data['adjacencyList'])
        self.vertex_size = len(adjacency)
        self.edges = set(Graph._to_edge(int(u), int(v)) for u in adjacency for v in adjacency[u])
        self.hamiltonianPath = None
        
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

    def to_json(self):
        return {
            "HoGId" : self.HoG_id,
            "vertexSize" : self.vertex_size,
            "edges" : sorted(list(self.edges)),
        }
