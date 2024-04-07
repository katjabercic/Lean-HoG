import sys
from threading import Timer
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Glucose4, Solver, Cadical195, MinisatGH

from graph import Graph
from downloadGraph import download_graph

def x(n,i,j):
    return (n*i)+j+1

def y(n,i,j):
    return (n*j)+i+1

def var_x(n,k):
    s = abs(k)
    j = (s - 1) % n
    return (1 if k > 0 else -1, (s-1) // n,j)

def var_y(n,k):
    s = abs(k)
    i = (s - 1) % n
    if k > 0:
        return f"x_{i},{(s-1) // n}"
    else:
        return f"-x_{i},{(s-1) // n}"

def to_vars_x(n, fmla):
    return [[var_x(n,k) for k in cl] for cl in fmla]

def to_vars_y(n, fmla):
    return [[var_y(n,k) for k in cl] for cl in fmla]

def sol_to_path(n, sol):
    path = [None] * n
    for k in sol:
        (v, i, j) = var_x(n, k)
        if v > 0:
            path[j] = i
    return path

def sol_to_cycle(n, sol):
    cycle = []
    for k in sol:
        if k > 0:
            i = (k - 1) % n
            cycle.append(i)
    return cycle

def encode_hamiltonian_path(G : Graph):
    # Vertices are 0-indexed, while CNF variables are 1-indexed
    n = G.vertex_size
    A = []
    B = []
    C = []
    D = []
    E = []
    for i in range(n):
        A.append([x(n,i,j) for j in range(n)])
    for j in range(n):
        B.append([x(n,i,j) for i in range(n)])
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if j != k:
                    C.append([-x(n,i,j), -x(n,i,k)])
    for j in range(n):
        for i in range(n):
            for k in range(n):
                if i != k:
                    D.append([-x(n,i,j), -x(n,k,j)])
    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                # Have to be careful, because we only have i < j in our list
                # So we have to check both
                if ((i,j) in G.edges or (j,i) in G.edges): 
                    continue
                else:
                    E.append([-x(n,i,k), -x(n,j,k+1)])
    return A + B + C + D + E

def interrupt(s):
    s.interrupt()

def encode_hamiltonian_cycle(G : Graph):
    # Vertices are 0-indexed, while CNF variables are 1-indexed
    n = G.vertex_size
    A = []
    B = []
    C = []
    D = []
    E = []
    for i in range(n):
        A.append([y(n,i,j) for j in range(n+1)])

    for j in range(n+1):
        B.append([y(n,i,j) for i in range(n)])

    for i in range(n):
        for j in range(n):
            for k in range(n):
                if j != k:
                    C.append([-y(n,i,j), -y(n,i,k)])

    for j in range(n+1):
        for i in range(n):
            for k in range(n):
                if i != k:
                    D.append([-y(n,i,j), -y(n,k,j)])

    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                # Have to be careful, because we only have i < j in our list
                # So we have to check both
                if ((i,j) in G.edges or (j,i) in G.edges): 
                    continue
                else:
                    E.append([-y(n,i,k), -y(n,j,k+1)])
    first_pos = [[y(n,0,0)]]
    last_pos = [[y(n,0,n)]]
    return A + B + C + D + E + first_pos + last_pos

def find_hamiltonian_path(G : Graph):
    print(f'Computing Hamiltonian path for {G.HoG_id}')
    enc = encode_hamiltonian_path(G)
    n = G.vertex_size
    with MinisatGH(bootstrap_with=enc, use_timer = True) as solver:
        timer = Timer(5, interrupt, [solver])
        timer.start()
        if solver.solve_limited(expect_interrupt=True):
            print('formula is satisfiable')
            print('Time: {0:.2f}s'.format(solver.time()))
            model = solver.get_model()
            path = sol_to_path(n, model)
            # print(f'hamiltonianPath: {path}')
            return path
        else:
            print('formula is unsatisfiable or timeout')
            print('Time: {0:.2f}s'.format(solver.time()))
            return None

def find_hamiltonian_cycle(G : Graph):
    print('Computing Hamiltonian cycle')
    enc = encode_hamiltonian_cycle(G)
    n = G.vertex_size
    with MinisatGH(bootstrap_with=enc, use_timer = True) as solver:
        timer = Timer(5, interrupt, [solver])
        timer.start()
        if solver.solve_limited(expect_interrupt=True):
            print('formula is satisfiable')
            print('Time: {0:.2f}s'.format(solver.time()))
            model = solver.get_model()
            cycle = sol_to_cycle(n, model)
            print(f'sol: {cycle}')
            return cycle
        else:
            print('formula is unsatisfiable or timeout')
            print('Time: {0:.2f}s'.format(solver.time()))
            return None

def find_all_hamiltonian_paths(destDir : str):
    for id in range(52000):
        try: 
            graphs = download_graph(destDir, id, id)
            if len(graphs) < 1:
                continue
            G = graphs[0]
            path = find_hamiltonian_path(G)
            G.hamiltonianPath = path
        except KeyboardInterrupt:
            print("System interrupt")
            sys.exit()

def find_all_hamiltonian_cycles(destDir : str):
    for id in range(1100, 52000):
        try: 
            graphs = download_graph(destDir, id, id)
            if len(graphs) < 1:
                continue
            G = graphs[0]
            path = find_hamiltonian_cycle(G)
            G.hamiltonianPath = path
        except KeyboardInterrupt:
            print("System interrupt")
            sys.exit()

if __name__ == '__main__':
    # find_all_hamiltonian_cycles()
    destDir = sys.argv[1]
    Path(destDir).mkdir(parents=True, exist_ok=True)
    id = sys.argv[2]
    graphs = download_graph(destDir, id, id)
    G = graphs[0]
    p = find_hamiltonian_path(G)
    G.hamiltonianPath = p
    print(p)
