# HoG-Lean

Sage code to get `graph6` for some small graphs.

```
# https://doc.sagemath.org/html/en/reference/graphs/index.html

arr = []
arr.append(graphs.EmptyGraph()) # empty
arr.append(graphs.PathGraph(3) + graphs.PathGraph(2)) # two components
arr.append(graphs.CompleteGraph(3)) # triangle
arr.append(graphs.PetersenGraph()) # Petersen
arr.append(graphs.FibonacciTree(4)) # tree

for g in arr:
    print(g.graph6_string())
for g in arr:
    g.show()
```
