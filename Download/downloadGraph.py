import os
import sys
import json
import requests
from pathlib import Path

from graph import Graph
from jsonEncoder import GraphEncoder

def download_graph(destDir : str, id : int):
    print(f'Downloading graph with ID {id}.')
    with requests.get(f'https://houseofgraphs.org/api/graphs/{id}') as response:
        if not response:
            sys.stderr.write(f"failed to download graph {id}")
        graph = Graph(id, response.json())
        with open(os.path.join(destDir, "{0}.json".format(id)), 'w') as fh:
            json.dump(graph, fh, cls=GraphEncoder)
            print(f"\rID {id} downloaded.", end=None)

if __name__ == '__main__':
    destDir = sys.argv[1]
    Path(destDir).mkdir(parents=True, exist_ok=True)
    id = int(sys.argv[2])
    download_graph(destDir, id)
