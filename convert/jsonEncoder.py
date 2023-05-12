import json

from graph import Edge, Graph
from treeSet import Tree
from treeMap import Map, TreeMap
from components_certificate import ComponentsCertificate

class GraphWithInvariants():
    graph : Graph

    def __init__(self, graph : Graph):
        self.graph = graph
    
    def to_json(self):
        return {
            "graph" : self.graph,
            "edgeSize" : self.graph.edge_size(),
            "componentsCertificate" : ComponentsCertificate(self.graph)
        }

class GraphEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, Edge):
            return obj.to_json()
        elif isinstance(obj, Graph):
            return obj.to_json()
        elif isinstance(obj, Tree):
            return obj.to_json()
        elif isinstance(obj, TreeMap):
            return obj.to_json()
        elif isinstance(obj, Map):
            return obj.to_json()
        elif isinstance(obj, ComponentsCertificate):
            return obj.to_json()
        elif isinstance(obj, GraphWithInvariants):
            return obj.to_json()
        else:
            # Let the base class default method raise the TypeError
            return json.JSONEncoder.default(self, obj)
