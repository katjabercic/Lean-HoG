import sys
import os
import json
import requests
from graph import Graph
from pathlib import Path
from jsonEncoder import GraphEncoder

def search_hog(destDir : str, data, search_hash):
    url = "https://houseofgraphs.org/api/enquiry"
    headers = {"content-type" : "application/json"}
    final_path = f"{destDir}/{search_hash}"
    
    if Path(final_path).exists():
        sys.exit(0)
    else:
        try:
            response = requests.post(url, headers=headers, data=data)
            response_json = response.json()

            if int(response_json['page']['totalElements']) > 0:
                for res in response_json['_embedded']['graphSearchModelList']:
                    G = Graph(res['graphId'], res)
                    Path(final_path).mkdir(parents=True, exist_ok=True)
                    with open(os.path.join(final_path, f"{G.HoG_id}.json"), 'w') as fh:
                        json.dump(G, fh, cls=GraphEncoder)
                    
            else:
                sys.exit(-1)

        except Exception as e:
            sys.stderr.write(e)
            sys.exit(1)

if __name__ == '__main__':
    destDir = sys.argv[1]
    Path(destDir).mkdir(parents=True, exist_ok=True)
    data = sys.argv[2]
    search_hash = sys.argv[3]
    search_hog(destDir, data, search_hash)