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
                # Nothing downstream works without the metadata, so this is fatal
                # rather than a warning to carry on past.
                raise RuntimeError(
                    f'Failed to download invariants info: HTTP {response.status_code}')
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
        """
        The invariant values for one graph, or None if HoG does not have them.

        Note a nonexistent id answers 200 here with a body holding only `_links`,
        so the status code on its own is not enough to tell.
        """
        with requests.get(self.invariants_url(id)) as response_inv:
            if not response_inv:
                sys.stderr.write(
                    f"Failed to download invariants for graph {id}: "
                    f"HTTP {response_inv.status_code}\n")
                return None
            invariants = response_inv.json()
        if "_embedded" not in invariants:
            sys.stderr.write(f"HoG has no invariants for graph {id}.\n")
            return None
        return invariants

    def download_graph(self, id : int) -> bool:
        """
        Download one graph into the cache directory. Returns whether it was written.

        HoG ids are not contiguous, so a missing id is an ordinary outcome of
        walking a range and reported as a skip rather than raised.
        """
        print(f'Downloading graph with ID {id}.')
        with requests.get(self.graph_url(id)) as response:
            if not response:
                sys.stderr.write(
                    f"Failed to download graph {id}: HTTP {response.status_code}\n")
                return False
            graph_data = response.json()
        raw_invariants = self._get_invariants(id)
        if raw_invariants is None:
            return False
        invariants = Invariants(raw_invariants, self.invariants_metadata)
        graph = Graph(id, graph_data, invariants)
        with open(os.path.join(self.dest_dir, "{0}.json".format(id)), 'w') as fh:
            json.dump(graph, fh, cls=GraphEncoder)
        print(f"\rDownloaded graph with ID {id}.", end=None)
        return True

if __name__ == '__main__':
    gc = GraphsCache(dest_dir = sys.argv[1])
    id = int(sys.argv[2])
    sys.exit(0 if gc.download_graph(id) else 1)
