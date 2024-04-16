import os
import sys
import json
import requests
from pathlib import Path

def download_metadata(destDir : str):
    print(f'Downloading invariants infor.')
    invariants_url = f'https://houseofgraphs.org/api/invariants'
    with requests.get(invariants_url) as response:
        if not response:
            sys.stderr.write(f"failed to download invariants info")
        with open(os.path.join(destDir, "HoG-invariants.json".format(id)), 'w') as fh:
            json.dump(response.json(), fh)
            print(f"\rInvariants downloaded.", end=None)

if __name__ == '__main__':
    destDir = sys.argv[1]
    Path(destDir).mkdir(parents=True, exist_ok=True)
    download_metadata(destDir)
