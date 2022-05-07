import os
import subprocess
import re
import time
from datetime import datetime

timestamp = datetime.now().strftime("%Y-%m-%d-%H-%M")
test_log=f'tests/test_log_{timestamp}.csv'
subprocess_io_location = "/home/jure/Documents/process_io/bin/proccess_io"

print(timestamp)

with open(test_log, 'a', encoding='utf-8') as outfile:
    outfile.write("vertex_size,edge_size,time,memory,olean_size\n")
    for i in range(171):
        print(i)
        graph_number = f'{i * 100 + 1:05d}'
        lean_file_location = f'/home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_{graph_number}'

        # Create the lean file with the graph
        convert = subprocess.run(["make", "convert", f'SKIP={i*100}', "LIMIT=1"], stdout=subprocess.PIPE)
        
        # Parse the lean file to get the number of vertices and number of edges
        # The previous command might not have created the file yet once the python line completes
        while not os.path.exists(f'{lean_file_location}.lean'):
            time.sleep(1)
            print("wait")

        with open(f'{lean_file_location}.lean', "r") as leanfile:
            for line in leanfile:
                match_vsize = re.search("vertex_size := (\d+)", line)
                if match_vsize:
                    vertex_size = match_vsize.group(1)
                match_esize = re.search("edge_size := (\d+)", line)
                if match_esize:
                    edge_size = match_esize.group(1)
        outfile.write(vertex_size + "," + edge_size + ",")

        # Run lean on the converted files and time the execution
        timed = subprocess.run(["/usr/bin/time", "lean", "--make", "--memory=25000", "src/hog/data"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        
        match = re.search("^(\d+\.\d+)user", timed.stderr.decode("utf-8"))
        outfile.write(match.group(1) + ",")
        outfile.flush()

        if subprocess_io_location:
            perf = subprocess.run([subprocess_io_location, "lean", "--make", "--memory=25000", "src/hog/data"], stdout=subprocess.PIPE)
            match = re.search("maxrss:.*(\d+)", perf.stdout.decode("utf-8"))
            outfile.write(match.group(1) + ",")
            outfile.flush()

        # Get the olean file size and add it to the log file
        stats = subprocess.run(["stat", f'--printf=%s',  f'{lean_file_location}.olean'], stdout=subprocess.PIPE)
        outfile.write(stats.stdout.decode("utf-8"))

        outfile.write("\n")
        outfile.flush()

print("Done")