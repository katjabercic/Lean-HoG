import json

from graph import Graph
from Invariant.ConnectedComponents import ConnectedComponentsCertificate
from Invariant.HamiltonianPath import HamiltonianPathCertificate
from Invariant.NeighborhoodMap import NeighborhoodMap

class GraphEncoder(json.JSONEncoder):
    def default(self, graph):
        if isinstance(graph, Graph):
            g = {
                "hogId": graph.HoG_id,
                "graph": graph.to_json(),
                "connectedComponents": ConnectedComponentsCertificate(graph).to_json(),
                "neighborhoodMap": NeighborhoodMap(graph).to_json(),
                "rawHoG": graph.invariants.to_json()
            }
            return g
        else:
            # Let the base class default method raise the TypeError
            return json.JSONEncoder.default(self, graph)

class HamiltonianPathEncoder(json.JSONEncoder):
    def default(self, hamiltonianPath):
        if isinstance(hamiltonianPath, HamiltonianPathCertificate):
            return hamiltonianPath.to_json()
        else:
            # Let the base class default method raise the TypeError
            return json.JSONEncoder.default(self, hamiltonianPath)