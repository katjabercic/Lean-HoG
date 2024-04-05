import sys
import os
import json
from pathlib import Path
from graph import Graph
from jsonEncoder import HamiltonianPathEncoder
from satEncoding import find_hamiltonian_path
from Invariant.HamiltonianPath import HamiltonianPathCertificate

destDir = os.path.join("build", "invariants", "hamiltonianPath")

def edgeListToAdjacencyList(vertexSize : int, edgeList : list[int]):
    adjacency = [[] for i in range(vertexSize)]
    for (i,j) in edgeList:
        nbhd_i = adjacency[i]
        nbhd_j = adjacency[j]
        adjacency[i] = [j] + nbhd_i
        adjacency[j] = [i] + nbhd_j
    return {
        "adjacencyList" : adjacency
    }

if __name__ == "__main__":
    Path(destDir).mkdir(parents=True, exist_ok=True)
    graphId = sys.argv[1]
    vertexSize = int(sys.argv[2])
    edgeList = json.loads(sys.argv[3])
    data = edgeListToAdjacencyList(vertexSize, edgeList)
    G = Graph(graphId, data)
    path = find_hamiltonian_path(G)
    hamiltonian_path = HamiltonianPathCertificate(G, path)
    with open(os.path.join(destDir, "{0}.json".format(graphId)), 'w') as fh:
        json.dump(hamiltonian_path, fh, cls=HamiltonianPathEncoder)