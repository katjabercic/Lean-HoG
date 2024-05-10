import os
import sys
import json
import requests
from pathlib import Path

from graph import Graph
from invariants import Invariants
from jsonEncoder import GraphEncoder

class GraphsCache():

    HoG_API_url = 'https://houseofgraphs.org/api'
    graphs_API_url = f'{HoG_API_url}/graphs'
    invariants_API_url = f'{HoG_API_url}/invariants'

    def __init__(self, dest_dir : str) -> None:
        self.dest_dir = dest_dir
        Path(dest_dir).mkdir(parents=True, exist_ok=True)
        self.invariants_path = os.path.join(dest_dir, 'invariants.json')
        self.invariants_metadata = self._get_metadata()

    def _download_metadata(self):
        """Download invariant metadata from HoG"""
        print(f'Downloading invariants metadata.')
        with requests.get(self.invariants_API_url) as response:
            if not response:
                sys.stderr.write(f'Failed to download invariants info')
            with open(self.invariants_path, 'w') as fh:
                json.dump(response.json(), fh)
                print(f'\rInvariants downloaded.', end=None)

    def _get_metadata(self):
        """Load invariant metadata (download if the file does not exist)"""
        if not os.path.exists(self.invariants_path):
            self._download_metadata()
        with open(self.invariants_path) as fh:
            return json.load(fh)

    @staticmethod
    def graph_url(id):
        return f'{GraphsCache.graphs_API_url}/{id}'
    
    @staticmethod
    def invariants_url(id):
        return f'{GraphsCache.graph_url(id)}/invariants'

    def _get_invariants(self, id : int):
        invariants = None
        with requests.get(self.invariants_url(id)) as response_inv:
            if response_inv:
                invariants = response_inv.json()
            else:
                sys.stderr.write(f"Failed to download invariants for graph {id}")
        return invariants

    def download_graph(self, id : int):
        print(f'Downloading graph with ID {id}.')
        with requests.get(self.graph_url(id)) as response:
            if not response:
                sys.stderr.write(f"Failed to download graph {id}")
            invariants = Invariants(self._get_invariants(id), self.invariants_metadata)
            graph = Graph(id, response.json(), invariants)
            with open(os.path.join(self.dest_dir, "{0}.json".format(id)), 'w') as fh:
                json.dump(graph, fh, cls=GraphEncoder)
                print(f"\rDownloaded graph with ID {id}.", end=None)

if __name__ == '__main__':
    gc = GraphsCache(dest_dir = sys.argv[1])
    id = int(sys.argv[2])
    gc.download_graph(id)
