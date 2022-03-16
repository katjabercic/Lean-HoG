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

def c_representation(name, vertices):
    c = f'  c := λ v : fin {name}.vertex_size,\n    match v with\n'
    for v in vertices:
        c += f'    | ⟨ {v.id}, _ ⟩ := {v.c}\n'
    c += '    | ⟨ _ , cond ⟩ := 0\n    end,'
    return c

def h_representation(name, vertices):
    h = f'  h := λ v : fin {name}.vertex_size,\n    match v with\n'
    for v in vertices:
        h += f'    | ⟨ {v.id}, _ ⟩ := {v.h}\n'
    h += '    | ⟨ _ , cond ⟩ := 0\n    end,'
    return h

def connect_edges_representation(name, vertices):
    n = len(vertices)
    h = f'  connect_edges := λ u v : fin {name}.vertex_size,\n    match u, v with\n'
    for i in range(n):
        for j in range(n):
            h += f'    | ⟨ {i}, _ ⟩, ⟨ {j}, _ ⟩ := begin intro _, bool_reflect end\n'
    h += f'    | ⟨ _, _ ⟩, ⟨ _, _ ⟩ := sorry\n'
    h += f'    end,'
    return h

def root_representation(roots):
    num_components = len(roots)
    root_rep = f'  root := λ i : fin {num_components},\n    match i with\n'
    for root in roots:
        root_rep += f'    | ⟨ {root[0]}, _ ⟩ := ⟨ {root[1]}, by bool_reflect ⟩\n'
    root_rep += f'    | _ := ⟨ 0, by bool_reflect ⟩\n    end,'
    return root_rep

def is_root_representation(roots):
    num_components = len(roots)
    root_rep = f'  is_root := λ i : fin {num_components},\n    match i with\n'
    for root in roots:
        root_rep += f'    | ⟨ {root[0]}, _ ⟩ := ⟨ by bool_reflect, by bool_reflect ⟩\n'
    root_rep += f'    | _ := ⟨ sorry, sorry ⟩\n    end,'
    return root_rep

def uniqueness_of_roots_representation(name, vertices):
    h = f'  uniqueness_of_roots := λ v : fin {name}.vertex_size,\n    match v with\n'
    for v in vertices:
        if v.h == 0:
            h += f'    | ⟨ {v.id}, _ ⟩ := by bool_reflect\n'
        else:
            h += f'    | ⟨ {v.id}, _ ⟩ := by contradiction\n'            
    h += '    | ⟨ _ , cond ⟩ := sorry\n    end,'
    return h

def next_representation(name, vertices):
    h = f'  next := λ v : fin {name}.vertex_size,\n    match v with\n'
    for v in vertices:
        if v.next:
            h += f'    | ⟨ {v.id}, _ ⟩ := ⟨ {v.next.id}, by bool_reflect ⟩\n'
    h += '    | ⟨ _ , cond ⟩ := ⟨ 0, by bool_reflect ⟩\n    end,'
    return h

def height_cond_representation(name, vertices):
    h = f'  height_cond := λ v : fin {name}.vertex_size,\n    match v with\n'
    for v in vertices:
        if v.h == 0:
            h += f'    | ⟨ {v.id}, cond ⟩ :=\n    begin\n      intro h,\n      by_contra,\n      have H : {name}_witness._match_1 ⟨{v.id}, cond⟩ = {v.id},\n      bool_reflect,\n      sorry\n    end\n'
        else:
            h += f'    | ⟨ {v.id}, cond ⟩ :=\n    begin\n      intro h,\n      split,\n      apply (to_bool_iff ({name}.edge (fin.mk {v.next.id} _) (fin.mk {v.id} _))).mp,\n      exact edge_{v.next.id}_{v.id},\n      bool_reflect\n    end\n'
    h += '    | _ := sorry\n    end,'
    return h

def edge_lemma_representation(name, s, t):
    l = f'lemma edge_{s}_{t} : @decidable.to_bool\n'
    l += f'  ({name}.edge (fin.mk {s} (by bool_reflect)) (fin.mk {t} (by bool_reflect)))\n'
    l += f'  ({name}.edge_decidable (fin.mk {s} (by bool_reflect)) (fin.mk {t} (by bool_reflect)))\n'
    l += '  = tt := by refl'
    return l

def lean_representation(name, vertices, roots):
    representation = ''
    for vertex in vertices:
        if vertex.next:
            representation += edge_lemma_representation(name, vertex.next.id, vertex.id) + '\n\n'

    representation += f'def {name}_witness : num_components_witness :=\n'
    representation += f'let H : {name}.vertex_size = {len(vertices)} := by bool_reflect in\n'
    representation += f'{{ G := {name},\n'
    representation += f'  num_components := {len(roots)},\n'
    representation += c_representation(name, vertices) + '\n'
    representation += h_representation(name, vertices) + '\n'
    representation += connect_edges_representation(name, vertices) + '\n'
    representation += root_representation(roots) + '\n'
    representation += is_root_representation(roots) + '\n'
    representation += uniqueness_of_roots_representation(name, vertices) + '\n'
    representation += next_representation(name, vertices) + '\n'
    representation += height_cond_representation(name, vertices) + '\n}'

    return representation

# nbhds = [(0, [4]), (1, [4]), (2,[3]), (3,[2,4]), (4,[0,1,3])]

# vertices = compute_components(nbhds)
# print(vertices)