# Lean-HoG

A library for computational graph theory in [Lean 4](https://leanprover.github.io), with emphasis on verification of large datasets of graphs; in particular the [House of Graphs](https://houseofgraphs.org) (HoG).

## Prerequisites

You need the following software:

* **[Lean 4](https://lean-lang.org) proof assistant**: Install Lean 4 by following [these instructions](https://leanprover-community.github.io/get_started.html). When successful, you should have the executables `elan` (for installing and updating versions of Lean), `lean` itself, and `lake` (the Lean build system).
* **([Visual Studio Code](https://code.visualstudio.com))**: the editor that has good Lean support.
* **[Node.js and `npm` cli](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)**. 
* **[Python](https://www.python.org)** version 3, with the [requests](https://pypi.org/project/requests/)  library, which you can install with `pip3 install requests`.


On MacOS you can use [Homebrew](https://brew.sh) to install Visual Studio Code and `Node.js` with
```
brew install npm
brew install --cask visual-studio-code
```

### SAT solving

For using the SAT solving facilities of the library (e.g. computing Hamiltonian paths) you need the following:

* A modern SAT solver capable of producing LRAT proofs of unsatisfiability,
  we recommend **[CaDiCaL](https://github.com/arminbiere/cadical)**.

Unsatisfiability proofs are checked by Lean's built-in verified LRAT checker;
no separate proof-checker executable is required.

Once you have installed the SAT solver, set `leanHoG.solverCmd` in Lean to the
location of the solver executable.

## Installation

To install all dependencies and compile Lean-HoG, run this command from the
Lean-HoG directory:

```shell
lake build
```

Lake installs the Lean version pinned in `lean-toolchain`, fetches the package
dependencies, installs the JavaScript dependencies, builds the graph
visualization widget, and then compiles Lean-HoG. The widget does not need to be
built separately. Mathlib's update hook also fetches its cached build artifacts
automatically, so there is no separate cache command to run.

## Usage

The library uses Python to interact with the HoG database and process the data
before it's imported in Lean.
To make Lean aware of the location of your Python executable set
```
set_option leanHoG.pythonExecutable <path-to-python>
```

Open the file [`Examples.lean`](Examples.lean) to check whether the example graphs load successfully.

### Downloading graphs

To download graphs from the [House of Graphs](https://houseofgraphs.org/) (HoG) you can
use the `#download <graphName> <hog_id>` command. 
It downloads the graphs with House of Graphs ID `hog_id` and loads it into the variable `graphName`.

You can check that it loaded it with `#check <graphName>`.

**Note**: To download the graph it uses an external python script. The location of the python executable is provided by the user option `leanHoG.pythonExecutable`.

**Note**: The python environment is expected to have the requests library installed.

#### Example
```lean
#download Petersen 660
#check Petersen
```


### Reading graphs from graph6

[graph6](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) is nauty's encoding of an undirected simple graph as a short string of printable ASCII, and is what `geng`, `nauty`, `networkx`, SageMath and the House of Graphs hand out. HoG's `canonicalForm` field is a graph6 string.

`load_graph_from_g6 <graphName> <g6>` loads the graph encoded by a graph6 string:

```lean
load_graph_from_g6 Petersen "IsP@OkWHG"
#show Petersen
#eval Petersen.numberOfConnectedComponents
```

`load_graphs_from_g6_file <graphName> <file>` loads every graph in a graph6 file, one per line as `geng` writes them, into `graphName_0`, `graphName_1`, … in the order the lines appear. Blank lines and a lone `>>graph6<<` header line are skipped.

```lean
load_graphs_from_g6_file Sample "examples/hog-sample.g6"
#show Sample_0
```

Each graph in the file becomes a separate compiled declaration, so a file with thousands of lines takes a correspondingly long time to elaborate.

Neither command attaches any invariant certificate, so invariants of a graph read from graph6 are decided by search rather than read off a certificate.

`Graph.toGraph6` goes the other way, encoding a graph under its own vertex labelling:

```lean
#eval Petersen.toGraph6
```

Only graph6 is supported; sparse6, the `:`-prefixed format, is not.


### Visualization widget

Lean-HoG can visualize the imported graphs in the Lean infoview using 
[widgets](https://lean-lang.org/lean4/doc/examples/widgets.lean.html),
which work by running Javascript in the Infoview.
The visualization uses the [cytoscape.js](https://js.cytoscape.org/) javascript library.


Try them out by opening the `Examples.lean` file and clicking on the line `#show Cycle7`. In the info view you should now see something like this:
![image](https://github.com/katjabercic/Lean-HoG/assets/6967728/f4ee94ab-4d31-4192-ac80-7e35323e5c4b)

### Search the House of Graphs from Lean

You can query the House of Graphs database from within Lean via the command `#search`.
To use it you have to construct a valid `hog_query` and enclose it into
`hog{ }` syntax. It has the following syntax:
```
hog_query q ::= boolean_invariant = b | numerical_invariant op x | query_formula op query_formula | ( q ) | q ∧ q | q ∨ q
```
where `b` is a boolean value, `x` is a numerical value
(`Int` for invariants with integral values, `Float` for invariants with continous values),
```
op ::= < | <= | > | >= | =
```
and 
```
query_formula f ::= x | numerical_invariant | f + f | f - f | f / f | f * f
```
The list of available invariants can be found in the [House of Graphs documentation](https://houseofgraphs.org/help#invariants).
The invariants use [lower camel case](https://en.wikipedia.org/wiki/Camel_case).

#### Example

```
#search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }
```

Should display the following in the Infoview:

```
Found 9 graphs satisfying given query
Found solution hog_302
Found solution hog_300
Found solution hog_296
Found solution hog_294
Found solution hog_310
Found solution hog_298
Found solution hog_304
Found solution hog_19655
Found solution hog_49432
```

The solutions point to the relevant page on the House of Graphs for each graph.
The graphs are also available in Lean, which you can check with e.g.
```lean
#check hog_302
```

### Search tactic

The library provides a tactic `find_example`,
which uses the search feature to close certain goals of the form
`∃ (G : Graph), P G` for Boolean predicates `P`.
The predicate `P` must be a conjunction of comparisons of invariants with
either invariants or numbers.
The supported invariants are those Lean-HoG currently implements. They include:
* `vertex size`
* `edge size`
* `minimum degree`
* `maximum degree`
* `number of connected components`
* `traceable`
* `non traceable`
* `bipartite`
* `non bipartite`
* `connected`
* `Hamiltonian`

#### Example

```lean
example : ∃ (G : Graph), G.traceable ∧ G.vertexSize > 3 ∧ 
  (G.minimumDegree < G.vertexSize / 2) := by
  find_example
```

## Raw data format

The JSON file should have the following structure.
```json
{
  "graph" : {
    "vertexSize" : <number of vertices>,
    "edges" : <list of edges>,
  },
  <invariants>
}
```

**IMPORTANT:** 
Lean-HoG expects all lists and maps, including the list of edges, to be **(lexicographically) ordered**.
In particular, edges must be **ordered pairs** (`[1, 2]`, never `[2, 1]`) and 
the list of edges should be lexicographically ordered.

### Examples of JSON encoding of graphs

Consult the (`examples`)[./examples] folder.

### Neighborhood map

```json
"neighborhoodMap" : {
  "neighbors" : <map vertices to their neighbors>,
}
```

### Connected components

```json
"connectedComponents" : {
  "val" : <number of components>,
  "component" : <map vertices to components>,
  "root" : <map components to their roots>,
  "next" : <map vertices to their parents, roots to roots>,
  "distToRoot" : <map vertices to their distance to the root>,
}
```

### Bipartite

```json
"bipartite" : {
  "color" : <map vertices to color, 0 or 1>,
  "vertex0" : <vertex with color 0>,
  "vertex1" : <vertex with color 1>,
},
```

### Odd closed walk

```json
"oddClosedWalk" : {
  "closedWalk" : <list of vertices>,
}
```
