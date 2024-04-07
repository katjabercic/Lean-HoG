from typing import Dict, Set

from graph import Graph

class NeighborhoodMap():
    """A map from vertices to their neighborhood sets."""

    graph : Graph
    neighbors : Dict[int, Set[int]]
    
    def __init__(self, graph : Graph):
        self.graph = graph
        self.neighbors = dict((u, set(graph.neighbors(u))) for u in graph.vertices())

    @staticmethod
    def _dict_to_sorted_pairs(d : Dict[int, Set[int]]):
        return sorted([[v, sorted(c)] for v, c in d.items()])

    def to_json(self):
        return {
            "neighbors" : sorted([[v, sorted(c)] for v, c in self.neighbors.items()])
        }
