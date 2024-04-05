import os
import sys
import json
import requests
from pathlib import Path

from graph import Graph
from jsonEncoder import GraphEncoder

destDir = os.path.join("build", "graphs")

def download_graph(minId : int, maxId : int):
    k = 0
    print(f'Downloading graphs with ID from {minId} to {maxId}.')
    for graphId in range(minId, maxId+1):
        with requests.get(f'https://houseofgraphs.org/api/graphs/{graphId}') as response:
            if not response:
                print(f"Skipping ID {graphId}")
                continue
            graph = Graph(graphId, response.json())
            with open(os.path.join(destDir, "{0}.json".format(graphId)), 'w') as fh:
                json.dump(graph, fh, cls=GraphEncoder)
                print(f"\rID {graphId} downloaded.", end=None)
                k += 1
    print(f'Downloaded {k} graphs')

if __name__ == '__main__':
    Path(destDir).mkdir(parents=True, exist_ok=True)
    minId = int(sys.argv[1])
    maxId = int(sys.argv[2])
    download_graph(minId, maxId)
