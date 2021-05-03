# Lean-HoG

Integration of [Lean](https://leanprover.github.io) and [House of Graphs](http://hog.grinvin.org/).

## House of Graphs

Sage code to get [`graph6`](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) for some small graphs.

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
for g in arr:
    print(g.average_degree())
```

## `graphs.csv` structure

* graph in the `graph6` format
* is the graph connected? True/False
* number of vertices in the graph
* average degree

## HoG supported invariants

| Invariant                    | Description  |
|------------------------------|--------------|
| ***bool***                   |  |
| Acyclic                      | A graph is said to be acyclic if it contains no cycle.  |
| Bipartite                    | A graph G is bipartite if it is possible to partition the set of vertices of G into two subsets A and B such that every edge of G joins a vertex of A to a vertex of B. |
| Claw-Free                    | A graph is Claw-Free if it does not contain a K_{1,3} as an induced subgraph. |
| Connected                    | A graph G is connected if every pair of vertices in G are joined by a path. |
| Eulerian                     | A graph is Eulerian if it contains an Eulerian circuit. An Eulerian circuit is a closed walk which visits each edge of the graph exactly once. |
| Hamiltonian                  | A graph is Hamiltonian if it contains a Hamiltonian cycle. A Hamiltonian cycle is a cycle which contains every vertex of the graph. |
| Planar                       | A graph is Planar if it can be drawn in the plane without crossing edges. |
| Regular                      | A graph is said to be regular if all of the degrees of its vertices are equals. |
| ***int***                    |  |
| Chromatic Index              | The (edge) chromatic index of a graph G is the minimum number of different colors required to color the edges of G such that two edges incident to the same vertex have different colors. |
| Chromatic Number             | The chromatic number of a graph G is the minimum number of different colors required to color the vertices of G such that two adjacent vertices have different colors. |
| Circumference                | The circumference of a graph is the order of the largest subgraph of the graph that is a cyclic graph. |
| Clique Number                | The clique number of a graph G is the maximum cardinality of a clique in G. |
| Diameter                     | The diameter D of a graph G=(V,E) is the maximum distance between two vertices of G, i.e. the "longest shortest path" in G. |
| Edge Connectivity            | The edge connectivity of a graph G is the smallest number of edges of G whose deletion will cause G to not be connected. |
| Genus                        | The genus of a graph is the minimal integer n such that the graph can be drawn without crossing itself on a sphere with n handles (i.e. an oriented surface of genus n). Thus, a planar graph has genus 0, because it can be drawn on a sphere without self-crossing. |
| Girth                        | The girth of G is the length of the shortest cycle (if any) in G. |
| Longest Induced Cycle        | The order of the largest induced subgraph of the graph that is a cycle. |
| Longest Induced Path         | The number of edges of the longest induced path of the graph. |
| Matching Number              | The matching number of a graph G is the maximum cardinality of the maximal matchings of G. |
| Maximum Degree               | The maximum degree of a graph G=(V,E) is the maximum value amongst all the degrees of its vertices. |
| Minimum Degree               | The minimum degree of a graph G=(V,E) is the minimum value amongst all the degrees of its vertices. |
| Minimum Dominating Set       | The domination number of a graph G is the minimum cardinality of a set of vertices such that every vertices is either in the set or is a neighbor of a vertex in the set. |
| Number of Components         |  |
| Number of Edges              |  |
| Number of Triangles          |  |
| Number of Vertices           |  |
| Radius                       | Let G = (V,E) be a graph. The eccentricity of a vertex v in V is the maximum distance between v and any other vertex in V. The radius of G is the minimum eccentricity of its vertices. |
| Vertex Connectivity          | The vertex connectivity of a graph G is the smallest number of vertices of G whose deletion will cause G to be disconnected. |
| ***float***                  |  |
| Average Degree               | The average degree of a graph G is the (arithmetic) mean of the degrees of its vertices. |
| Density                      | The density of a graph G = (V,E) is the number of edges divided by the largest possible number of edges of the graph (i.e. |V|*(|V|-1)/2). |
| ***float***                  | various eigenvalues  |
| Algebraic Connectivity       | https://hog.grinvin.org/ShowInvariant.action?id=19 |
| Index                        | The index or spectral radius of a graph is the greatest eigenvalue of its adjacency matrix. |
| Laplacian Largest Eigenvalue | https://hog.grinvin.org/ShowInvariant.action?id=22 |
| Second Largest Eigenvalue    | The second largest eigenvalue of a graph is the second largest eigenvalue of its adjacency matrix. |
| Smallest Eigenvalue          | The smallest eigenvalue of a graph is the smallest eigenvalue of its adjacency matrix. |

## Lean

Assuming you have [installed Lean and Mathlib](https://leanprover-community.github.io/index.html), after cloning this repository, you should run

    leanproject build


