import re
import os

filename = "test_log_22-03-17-10-21"

tests = []
with open ("tests/" + filename, 'r') as file:
    test = []
    for line in file:
        if line.isspace():
            tests.append(test)
            test = []
        else:    
            test.append(line)


graphs = []

for test in tests:
    test_id = int(test[0])
    match = re.search("^(\d+\.\d+)user", test[1])
    if not match:
        print("Unable to parse time of test")
        continue
    time = float(match.group(1))
    match_memory = re.search("maxrss:.*?(\d+)", test[5])
    if not match_memory:
        print("Unable to parse memory usage of test")
        continue
    memory = int(match_memory.group(1))
    match_olean = re.search("olean size:.*?(\d+)", test[6])
    if not match_olean:
        print("Unable to parse olean size of test")
        continue
    olean_size = int(match_olean.group(1))
    graphs.append([str(test_id), str(time), str(memory), str(olean_size)])
    
# print(graphs)

with open('tests/' + filename + '.csv', 'w') as stats:
    stats.write('id,time,memory,olean size\n')
    for graph in graphs:
        stats.write(','.join(graph))
        stats.write('\n')