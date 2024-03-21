import os
import sys
import json
import requests
from pathlib import Path

from graph import Graph
from jsonEncoder import GraphEncoder, graph_to_json

def download_graph(graph_id_1 : str, graph_id_2 : str):
    a = int(graph_id_1)
    b = int(graph_id_2)
    graph_ids = range(min(a,b), max(a,b)+1)
    print(f'Downloading graphs: {graph_ids[0]}-{graph_ids[len(graph_ids)-1]}')
    for graph_id in graph_ids:
        try:
            url = f'https://houseofgraphs.org/api/graphs/{graph_id}'
            response = requests.get(url)

            # Parse the response and build and save the graph
            response_json = response.json()
            G = Graph(graph_id, response_json)

            buildDir = 'build'
            graphsDir = 'graphs'

            Path(f"{buildDir}/{graphsDir}").mkdir(parents=True, exist_ok=True)
            with open(os.path.join(buildDir, graphsDir, "{0}.json".format(graph_id)), 'w') as fh:
                json.dump(graph_to_json(G), fh, cls=GraphEncoder)
        except:
            print(f"Failed to download graph {graph_id}")

    print('Done')

if __name__ == '__main__':
    graph_id_1 = sys.argv[1]
    graph_id_2 = sys.argv[2]
    download_graph(graph_id_1, graph_id_2)
