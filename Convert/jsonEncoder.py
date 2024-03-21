import json

from graph import Graph

def graph_to_json(graph : Graph) -> dict:
    if graph.hamiltonianPath:
        return {
            "hogId" : graph.HoG_id,
            "graph" : graph,
            "pathData" : {
                "vertices": graph.hamiltonianPath
            }
        }
    else:
        return {
            "hogId" : graph.HoG_id,
            "graph" : graph,
        }

class GraphEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, Graph):
            return obj.to_json()
        else:
            # Let the base class default method raise the TypeError
            return json.JSONEncoder.default(self, obj)
