class Vertex:

    def __init__(self, id):
        self.id = id
        self.c = -1
        self.h = -1
        self.checked = False
        self.neighbors = []
        self.next = None

    def show_neighbors(self):
        s = '('
        for nb in self.neighbors:
            s+= str(nb.id) + ','
        s = s[:-1]
        s += ')'
        return s

    def __repr__(self) -> str:
        empty = '_'
        return f'{{id: {self.id}, c: {self.c}, h: {self.h}, next: {self.next.id if self.next else empty}}}]\n'


def compute_components(neighborhoods):
    n = len(neighborhoods)
    vertices = [Vertex(i) for i in range(n)]
    stack = [vertices[0]]

    for neighborhood in neighborhoods:
        ind = neighborhood[0]
        neighbors = neighborhood[1]
        for neighbor in neighbors:
            vertices[ind].neighbors.append(vertices[neighbor])

    c = -1
    for vertex in vertices:
        if not vertex.checked:
            stack.append(vertex)
        h = 0
        if stack:
            c += 1
        while stack:
            next = stack.pop()
            if next.checked:
                continue
            next.c = c
            next.h = h
            h += 1
            for neighbor in next.neighbors:
                if neighbor.checked == False:
                    stack.append(neighbor)
            next.checked = True

    for vertex in vertices:
        for nb in vertex.neighbors:
            if nb.h < 0:
                raise RuntimeError(f'Height of vertex {nb.id} is -1!')    
            if nb.h < vertex.h:
                vertex.next = nb
                break

    return vertices

# nbhds = [(0, [4]), (1, [4]), (2,[3]), (3,[2,4]), (4,[0,1,3])]

# vertices = compute_components(nbhds)
# print(vertices)