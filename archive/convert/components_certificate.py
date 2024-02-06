from typing import Tuple, List, Set, Dict, Any, AnyStr, Optional, Union

from graph import Graph
from treeMap import Map, TreeMap

class ComponentsCertificate():
    """A computational certificate for the connected components of a graph."""

    graph : Graph
    val : int # number of components
    component : Dict[int, int] # mapping from vertices to components
    root : Dict[int, int] # mapping from components to their roots
    nextVertex : Dict[int, int] # next vertex on the path to the root
    distToRoot : Dict[int, int] # distance to the component root
    
    def __init__(self, graph : Graph):
        self.graph = graph
        self.val = 0
        self.component = {}
        self.root = {}
        self.nextVertex = {}
        self.distToRoot = {}

        def sweep(v : int):
            for w in graph.neighbors(v):
                if w in self.component: continue
                else:
                    self.component[w] = self.component[v]
                    self.nextVertex[w] = v
                    self.distToRoot[w] = self.distToRoot[v] + 1
                    sweep(w)

        for v in range(graph.vertex_size):
            if v in self.component:
                # we processed this one before
                continue
            else:
                # set up v as the root
                self.component[v] = self.val
                self.root[self.val] = v
                self.nextVertex[v] = v
                self.distToRoot[v] = 0
                # sweep the component reachable from v
                sweep(v)
                # new component
                self.val += 1

    def to_json(self):
        emptyGraph = self.graph.is_empty()
        return {
            "val" : self.val,
            "component" : Map(emptyDomain=emptyGraph, defaultValue = 0, tree=TreeMap.from_dict(self.component)),
            "root" : Map(emptyDomain=emptyGraph, defaultValue=0, tree=TreeMap.from_dict(self.root)),
            "next" : Map(emptyDomain=emptyGraph, defaultValue=0, tree=TreeMap.from_dict(self.nextVertex)),
            "distToRoot" : Map(emptyDomain=emptyGraph, defaultValue=0, tree=TreeMap.from_dict(self.distToRoot)),
        }
