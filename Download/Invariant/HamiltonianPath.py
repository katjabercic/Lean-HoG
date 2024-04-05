from graph import Graph

class HamiltonianPathCertificate():
    """A computational certificate for a Hamiltonian path in a graph."""

    graph : Graph
    path : list[int]
    
    def __init__(self, graph : Graph, path : list[int]):
        self.graph = graph
        self.path = path

    def to_json(self):
        return {
            "path": self.path
        }
