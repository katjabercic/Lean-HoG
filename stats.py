import re

lines = []
with open ("test_log_21-12-24-15-08", 'r') as file:
    for line in file:
        lines.append(line)


graphs = []
for i in range(170):
    graph = lines[i*7:(i+1)*7]
    id, vertices, edges = graph[0].split(',')
    memory = graph[4][9:-1]
    size = graph[5][12:-1]
    graphs.append([id, vertices, edges[:-1], memory, size])


with open('stats.csv', 'w') as stats:
    stats.write('id,vertices,edges,memory,olean size\n')
    for graph in graphs:
        stats.write(','.join(graph))
        stats.write('\n')