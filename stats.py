import re

lines = []
with open ("test_log_22-02-03-13-47", 'r') as file:
    for line in file:
        lines.append(line)


graphs = []
for i in range(199):
    graph = lines[i*8:(i+1)*8]
    # id, vertices, edges = graph[0].split(',')
    memory = graph[3][9:-1]
    file_size = graph[6][12:-1]
    vertices = graph[7][14:-1]
    time = graph[4][0:4]
    graphs.append([str(i), vertices, time, memory, file_size])


with open('stats_22-02-03-13-47.csv', 'w') as stats:
    stats.write('id,vertices,time,memory,olean size\n')
    for graph in graphs:
        print(graph)
        stats.write(','.join(graph))
        stats.write('\n')