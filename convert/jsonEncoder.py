import json

from graph import Edge, Graph
from treeSet import Tree
from treeMap import Map, TreeMap
from components_certificate import ComponentsCertificate

def graph_to_json(graph : Graph) -> dict:
    nbhMap = TreeMap.from_dict({v : Tree.from_set(nbh)
                for (v, nbh) in graph.neighborhood_map().items()})
    return {
        "graph" : graph,
        "edgeSize" : graph.edge_size(),
        "neighborhoodMap" : Map(emptyDomain=graph.is_empty(), defaultValue=Tree(), tree=nbhMap),
        "componentsCertificate" : ComponentsCertificate(graph)
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
