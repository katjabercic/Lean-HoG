import os
import subprocess
import re
import time
from datetime import datetime

timestamp = datetime.now().strftime("%Y-%m-%d-%H-%M")
test_log=f'tests/test_log_{timestamp}.csv'
subprocess_io_location = "/home/jure/Documents/process_io/bin/process_io"

print(timestamp)
max_ind = 17 * 100 + 1
k = 10
start = time.time()
avg_time = 0
total_time = 0
with open(test_log, 'x', encoding='utf-8') as outfile:
    outfile.write("id,vertex_size,edge_size,time,memory,olean_size\n")
    for i in range(max_ind):
        t1_start = time.perf_counter()
        graph_number = f'{i * k + 1:05d}'
        lean_file_location = f'/home/jure/Documents/source-control/Lean-HoG/src/hog/data/hog_{graph_number}'
        outfile.write(graph_number + ",")

        # Create the lean file with the graph
        convert = subprocess.run(["make", "convert", f'SKIP={i*k}', "LIMIT=1"], stdout=subprocess.PIPE)
        
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
        timed = subprocess.run(["/usr/bin/time", "lean", "--make", "--memory=25000", f'{lean_file_location}.lean'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        
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
        t1_stop = time.perf_counter()
        elapsed = t1_stop - t1_start
        total_time += elapsed
        avg_time = (avg_time * i + elapsed) / (i+1)
        print(f'Processing graphs: {i} / {max_ind}, total elapsed time: {total_time}, average time: {avg_time}', end='\r')

print(f'Done, total time: {total_time}')