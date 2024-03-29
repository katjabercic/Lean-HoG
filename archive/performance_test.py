import sys
import os
import subprocess
import re
import time
from datetime import datetime
from argparse import ArgumentParser

def run_performance_tests(skip):

    timestamp = datetime.now().strftime("%Y-%m-%d-%H-%M")
    test_log=f'tests/test_log_{timestamp}.csv'
    subprocess_io_location = "./process_io/bin/process_io"
    convert_command = "convert-data"
    build_command = "build-graphs"

    try:
        subprocess.run(["gcc", "process_io/src/process_io.c", "-o", "process_io/bin/process_io"])
    except:
        print("Could not compile process_io, do you have gcc installed?")

    print(timestamp)
    max_ind = 20 * 100 + 1
    k = 10
    start = time.time()
    avg_time = 0
    total_time = 0
    with open(test_log, 'x', encoding='utf-8') as outfile:
        outfile.write("id,vertex_size,edge_size,time,memory,olean_size\n")

        # Clean the outputs first
        try:
            subprocess.run(["make", "clean-lean"], stdout=subprocess.PIPE)
            subprocess.run(["make", "clean-graphs"], stdout=subprocess.PIPE)
            subprocess.run(["make", "build-lean"], stdout=subprocess.PIPE)
        except Exception as e:
            print("Unable to clean and build lib")
            print(e)
            sys.exit(1)

        for i in range(skip, max_ind):
            t1_start = time.perf_counter()
            graph_number = f'{i * k + 1:05d}'
            lean_file_location = f'src/hog/data/Data/hog{graph_number}'
            olean_file_location = f'build/lib/Data/hog{graph_number}'
            outfile.write(graph_number + ",")

            # Create the lean file with the graph
            convert = subprocess.run(["make", convert_command, f'SKIP={i*k}', "LIMIT=1"], stdout=subprocess.PIPE)
            
            # Parse the lean file to get the number of vertices and number of edges
            # The previous command might not have created the file yet once the python line completes
            while not os.path.exists(f'{lean_file_location}.lean'):
                time.sleep(1)
                print("wait")

            with open(f'{lean_file_location}.lean', "r") as leanfile:
                for line in leanfile:
                    match_vsize = re.search("vertexSize := (\d+)", line)
                    if match_vsize:
                        vertex_size = match_vsize.group(1)
                    match_esize = re.search("edgeSize := (\d+)", line)
                    if match_esize:
                        edge_size = match_esize.group(1)
            outfile.write(vertex_size + "," + edge_size + ",")

            # Run lean on the converted files and time the execution
            try:
                process = subprocess.run("/usr/bin/time ./process_io/bin/process_io \"make -s build-graphs\"", stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
                match_time = re.search("^(\d+\.\d+)user", process.stderr.decode("utf-8"))
                outfile.write(match_time.group(1) + ",")
                match_memory = re.search("maxrss:.*(\d+)", process.stdout.decode("utf-8"))
                outfile.write(match_memory.group(1) + ",")
                outfile.flush()
            except Exception as e:
                print("An exception has occured, exiting")
                print(e)
                sys.exit(1)

            # Get the olean file size and add it to the log file
            try:
                stats = subprocess.run(["stat", f'--printf=%s',  f'{olean_file_location}.olean'], stdout=subprocess.PIPE)
                outfile.write(stats.stdout.decode("utf-8"))
            except Exception as e:
                print(e)
                sys.exit(1)

            outfile.write("\n")
            outfile.flush()
            t1_stop = time.perf_counter()
            elapsed = t1_stop - t1_start
            total_time += elapsed
            avg_time = (avg_time * i + elapsed) / (i+1)
            print(f'Processing graphs: {i} / {max_ind}, total elapsed time: {total_time}, average time: {avg_time}', end='\r')

    print(f'Done, total time: {total_time}')

if __name__ == "__main__":

    arg_parser = ArgumentParser()
    arg_parser.add_argument("--skip", type=int, default=0, required=False, dest="skip",
                        help="skip this many graphs initially")
    args = arg_parser.parse_args()

    run_performance_tests(skip=args.skip)
