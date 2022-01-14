from sys import stdin
from sys import stdout
from collections import defaultdict


def cycle_factors(f, n):
    cycles = []
    visited = set()

    def search(i):
        l = [i]
        j = f(i)
        while j != i:
            if j in visited:
                break
            visited.add(j)
            l.append(j)
            j = f(j)
        return l
    for i in range(n):
        if i in visited:
            continue
        visited.add(i)
        cycles.append(search(i))
    return cycles


def print_cycles(cycles):
    for cycle in cycles:
        print(" ".join(map(str, cycle)))


# if __name__ == "__main__":
#n = int(input())
f_def = [tuple(s.split()) for s in stdin]
n = len(f_def) - 1

ev_f = defaultdict(lambda: int(f_def[-1][1]))
for (x, y) in f_def[:-1]:
    ev_f[int(x)] = int(y)


def f(i): return ev_f[i]


cycles = cycle_factors(f, n)
with open("test.txt", 'w') as f:
    f.write(str(cycles))
print_cycles(cycles)
