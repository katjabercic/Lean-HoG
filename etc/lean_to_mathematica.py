def lean_to_mathematica(graph):
    g = graph
    for c in ['(', ')', '[', ']', ' ']:
        g = g.replace(c, '')
    g = g.split(',')
    edges = []
    for i in range(len(g) // 2):
        edges.append(g[2*i] + ' <-> ' + g[2*i+1])
    return 'Graph[{' + ', '.join(edges) + '}]'

g1 = "[(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8), (4, 9), (6, 9), (7, 9)]"
print(lean_to_mathematica(g1))

g2 = "[(0, 1), (1, 2), (3, 4)]"
print(lean_to_mathematica(g2))