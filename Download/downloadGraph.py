import os
import sys
import json
import requests
from pathlib import Path

from graph import Graph
from jsonEncoder import GraphEncoder

def download_graph(destDir : str, id : int):
    print(f'Downloading graph with ID {id}.')
    graph_url = f'https://houseofgraphs.org/api/graphs/{id}'
    with requests.get(graph_url) as response:
        if not response:
            sys.stderr.write(f"failed to download graph {id}")
        invariants = None
        with requests.get(f'{graph_url}/invariants') as response_inv:
            if response_inv:
                invariants = response_inv.json()
            else:
                sys.stderr.write(f"failed to download invariants for graph {id}")
        graph = Graph(id, response.json(), invariants)
        with open(os.path.join(destDir, "{0}.json".format(id)), 'w') as fh:
            json.dump(graph, fh, cls=GraphEncoder)
            print(f"\rID {id} downloaded.", end=None)

if __name__ == '__main__':
    destDir = sys.argv[1]
    Path(destDir).mkdir(parents=True, exist_ok=True)
    id = int(sys.argv[2])
    download_graph(destDir, id)
