# Lean-HoG

Incorporation of the [House of Graphs](http://hog.grinvin.org/) into [Lean](https://leanprover.github.io).

## Contributing

### Project structure

* [`etc`](./etc) - various irrelevant files
* [`data`](./data) - original HoG data files
* [`convert`](./convert) - Python scripts for converting HoG data to Lean code
* [`src`](./src) - Lean code

### How to compile the code

Assuming you have [installed Lean 3 and Mathlib](https://leanprover-community.github.io/index.html), after cloning this repository, you may run

* `make convert` - convert HoG data to Lean files
* `make build` or `leanpkg build` - compile all the Lean files
* `make clean` - delete the generated Lean files
* `make` to convert and build

Building all Lean files is currently not feasible. The default limit is set in the Makefile.
It is possible to provide two optional parameters:

* `LIMIT=n` processes only `n` graphs,
* `SKIP=m` skips the first `m` graphs.

## Obtaining House of graphs data

It is tricky to obtain the House of graphs data because the project only offers an interactive web page. We hhave downloaded the data, but are not allowed to share it publicly, so you will have to do it yourself. Place the data in the `data` folder.

If you have the data in a git repository, you may add it as a submodule:

	git submodule add <repository-with-hog-data> data


## Reading and references

### Lean

* [Logical verification 2020](https://github.com/blanchette/logical_verification_2020) - textbook
* [The Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/)
* [A Metaprogramming Framework for Formal Verification](https://leanprover.github.io/papers/tactic.pdf)
* [How to connect Mathematica and Lean](https://deepai.org/publication/an-extensible-ad-hoc-interface-between-lean-and-mathematica)

### Other

* [NAUTY](https://www.swmath.org/software/611) - computing authomorphism groups of graphs and digraphs (also computes canonical labellings)

## House of Graphs

The [House of Graphs](http://hog.grinvin.org/) is a database of simple graphs, encoded in the
[`graph6`](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) format, with a collection of precomputed invariants:

| Invariant                    | Type | Description  |
|------------------------------|------|--------------|
| Acyclic                      | `bool` | A graph is said to be acyclic if it contains no cycle.  |
| Bipartite                    | `bool` | A graph G is bipartite if it is possible to partition the set of vertices of G into two subsets A and B such that every edge of G joins a vertex of A to a vertex of B. |
| Claw-Free                    | `bool` | A graph is Claw-Free if it does not contain a K_{1,3} as an induced subgraph. |
| Connected                    | `bool` | A graph G is connected if every pair of vertices in G are joined by a path. |
| Eulerian                     | `bool` | A graph is Eulerian if it contains an Eulerian circuit. An Eulerian circuit is a closed walk which visits each edge of the graph exactly once. |
| Hamiltonian                  | `bool` | A graph is Hamiltonian if it contains a Hamiltonian cycle. A Hamiltonian cycle is a cycle which contains every vertex of the graph. |
| Planar                       | `bool` | A graph is Planar if it can be drawn in the plane without crossing edges. |
| Regular                      | `bool` | A graph is said to be regular if all of the degrees of its vertices are equals. |
| Chromatic Index              | `int` | The (edge) chromatic index of a graph G is the minimum number of different colors required to color the edges of G such that two edges incident to the same vertex have different colors. |
| Chromatic Number             | `int` | The chromatic number of a graph G is the minimum number of different colors required to color the vertices of G such that two adjacent vertices have different colors. |
| Circumference                | `int` | The circumference of a graph is the order of the largest subgraph of the graph that is a cyclic graph. |
| Clique Number                | `int` | The clique number of a graph G is the maximum cardinality of a clique in G. |
| Diameter                     | `int` | The diameter D of a graph G=(V,E) is the maximum distance between two vertices of G, i.e. the "longest shortest path" in G. |
| Edge Connectivity            | `int` | The edge connectivity of a graph G is the smallest number of edges of G whose deletion will cause G to not be connected. |
| Genus                        | `int` | The genus of a graph is the minimal integer n such that the graph can be drawn without crossing itself on a sphere with n handles (i.e. an oriented surface of genus n). Thus, a planar graph has genus 0, because it can be drawn on a sphere without self-crossing. |
| Girth                        | `int` | The girth of G is the length of the shortest cycle (if any) in G. |
| Longest Induced Cycle        | `int` | The order of the largest induced subgraph of the graph that is a cycle. |
| Longest Induced Path         | `int` | The number of edges of the longest induced path of the graph. |
| Matching Number              | `int` | The matching number of a graph G is the maximum cardinality of the maximal matchings of G. |
| Maximum Degree               | `int` | The maximum degree of a graph G=(V,E) is the maximum value amongst all the degrees of its vertices. |
| Minimum Degree               | `int` | The minimum degree of a graph G=(V,E) is the minimum value amongst all the degrees of its vertices. |
| Minimum Dominating Set       | `int` | The domination number of a graph G is the minimum cardinality of a set of vertices such that every vertices is either in the set or is a neighbor of a vertex in the set. |
| Number of Components         | `int` |  |
| Number of Edges              | `int` |  |
| Number of Triangles          | `int` |  |
| Number of Vertices           | `int` |  |
| Radius                       | `int` | Let G = (V,E) be a graph. The eccentricity of a vertex v in V is the maximum distance between v and any other vertex in V. The radius of G is the minimum eccentricity of its vertices. |
| Vertex Connectivity          | `int` | The vertex connectivity of a graph G is the smallest number of vertices of G whose deletion will cause G to be disconnected. |
| Average Degree               | `float` | The average degree of a graph G is the (arithmetic) mean of the degrees of its vertices. |
| Density                      | `float` | The density of a graph G = (V,E) is the number of edges divided by the largest possible number of edges of the graph (i.e. |V|*(|V|-1)/2). |
| various eigenvalues          | `float` |   |
| Algebraic Connectivity       | `float` | https://hog.grinvin.org/ShowInvariant.action?id=19 |
| Index                        | `float` | The index or spectral radius of a graph is the greatest eigenvalue of its adjacency matrix. |
| Laplacian Largest Eigenvalue | `float` | https://hog.grinvin.org/ShowInvariant.action?id=22 |
| Second Largest Eigenvalue    | `float` | The second largest eigenvalue of a graph is the second largest eigenvalue of its adjacency matrix. |
| Smallest Eigenvalue          | `float` | The smallest eigenvalue of a graph is the smallest eigenvalue of its adjacency matrix. |

The following special values are used in the database:

* `infinity`
* `undefined` - the value is not well-defined, or the data are missing in the database
* `Computation time out`
