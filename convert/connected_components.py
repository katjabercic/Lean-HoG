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
    roots = []

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
            if h == 0:
                roots.append((c,next.id))
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

    return (vertices, roots)

def c_representation(vertices):
    c = f'  c := fun v : ℕ => \n    match v with\n'
    for v in vertices:
        c += f'    | {v.id} => {v.c}\n'
    c += '    | _ => 0'
    return c

def h_representation(vertices):
    h = f'  h := fun v : ℕ => \n    match v with\n'
    for v in vertices:
        h += f'    | {v.id} => {v.h}\n'
    h += '    | _ => 0'
    return h

def connect_edges_representation(vertices):
    n = len(vertices)
    h = f'  connectEdges := by\n'
    h += f'      apply Tset.forallIsForall\n'
    h += f'      bool_reflect\n'
    return h

def root_representation(roots):
    num_components = len(roots)
    root_rep = f'  root := fun i : Fin {num_components} =>\n    match i with\n'
    for root in roots:
        root_rep += f'    | ⟨ {root[0]}, _ ⟩ => {root[1]}\n'
    root_rep += f'    | _ => 0'
    return root_rep

def is_root_representation(roots):
    num_components = len(roots)
    root_rep = f'  isRoot := fun i =>\n    match i with\n'
    for root in roots:
        root_rep += f'    | ⟨ {root[0]}, _ ⟩ => by bool_reflect\n'
    root_rep += f'    | _ => sorry'
    return root_rep

def uniqueness_of_roots_representation(vertices):
    h = f'  uniquenessOfRoots := fun v =>\n    match v with\n'
    for v in vertices:
        if v.h == 0:
            h += f'    | {v.id} => by bool_reflect\n'
        else:
            h += f'    | {v.id} => by simp\n'            
    h += '    | _ => sorry'
    return h

def next_representation(vertices):
    h = f'  next := fun v =>\n    match v with\n'
    for v in vertices:
        if v.next:
            h += f'    | {v.id} => {v.next.id}\n'
    h += '    | _ => 0,'
    return h

def height_cond_representation(vertices):
    h = f'  heightCond := fun v =>\n    match v with\n'
    for v in vertices:
        if v.h == 0:
            h += f'    | {v.id} => by\n      have nh : ¬ 0 < 0 := irrefl 0\n      simp\n'
        else:
            h += f'    | {v.id} => by\n      simp [edgeRelation, lt_by_cases]\n'
    h += '    | _ => sorry'
    return h


def lean_representation(name, vertices, roots):
    representation = ''

    representation += f'def {name}_witness : numComponentsWitness :=\n'
    representation += f'let H : {name}.vertexSize = {len(vertices)} := by bool_reflect\n'
    representation += f'{{ G := {name},\n'
    representation += f'  numComponents := {len(roots)},\n'
    representation += c_representation(vertices) + '\n'
    representation += h_representation(vertices) + '\n'
    representation += connect_edges_representation(vertices) + '\n'
    representation += root_representation(roots) + '\n'
    representation += is_root_representation(roots) + '\n'
    representation += uniqueness_of_roots_representation(vertices) + '\n'
    representation += next_representation(vertices) + '\n'
    representation += height_cond_representation(vertices) + '\n}'

    return representation