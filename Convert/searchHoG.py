import sys
import os
import json
import requests
from graph import Graph
from pathlib import Path
from jsonEncoder import GraphEncoder, graph_to_json

def search_hog(data, search_hash):
    url = "https://houseofgraphs.org/api/enquiry"
    headers = {"content-type" : "application/json"}
    buildDir = 'build'
    searchResDir = f'search_results_{search_hash}'
    
    if Path(f"{buildDir}/{searchResDir}").exists():
        sys.exit(0)
    else:
        try:
            response = requests.post(url, headers=headers, data=data)
            response_json = response.json()

            if int(response_json['page']['totalElements']) > 0:
                for res in response_json['_embedded']['graphSearchModelList']:
                    G = Graph(res['graphId'], res)

                    Path(f"{buildDir}/{searchResDir}").mkdir(parents=True, exist_ok=True)
                    with open(os.path.join(buildDir, searchResDir, f"{G.HoG_id}.json"), 'w') as fh:
                        json.dump(graph_to_json(G), fh, cls=GraphEncoder)
                    
            else:
                sys.exit(-1)

        except:
            sys.exit(1)

if __name__ == '__main__':
    data = sys.argv[1]
    search_hash = sys.argv[2]
    search_hog(data, search_hash)