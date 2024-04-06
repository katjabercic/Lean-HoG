# Lean-HoG

A library for computational graph theory in [Lean 4](https://leanprover.github.io), with emphasis on verification of large datasets of graphs; in particular the [House of Graphs](https://houseofgraphs.org).

## Installation and setup

Install Lean 4 by following [these instructions](https://leanprover-community.github.io/get_started.html).
When successful, you should have the executables `elan` (for installing and updating versions of Lean), `lean` itself, and `lake` (the Lean build system).

Before compiling and using Lean-HoG, run the following in the present folder:

* `elan update` to make sure you have an up-to-date version of Lean,
* `lake exe cache get` to get a cached version of Mathlib (or else wait for it to compile).

## Usage

Lean 4 is best used in interactive mode using the [Visual Studio Code](https://code.visualstudio.com) editor, please consult the Lean documentation.
Once you set it up, simply open the file [`Examples.lean`](Examples.lean), which should trigger compilation.

Alternatively, build the project from the command line:

* `lake build` to compile the Lean files,
* `lake clean` to remove the compiled Lean files.

It is possible to write or generate your own files with graphs for Lean-HoG. 
TODO format description.

### Downloading graphs

To download graphs from the [House of Graphs](https://houseofgraphs.org/) (HoG) website and import them into Lean
you're going to need:
* [Pyhton](https://www.python.org/) version 3 or higher.
* The [requests](https://pypi.org/project/requests/) library.

Run
* `lake exe download <id>` to download the graph with the ID `<id>`,
* `lake exe download <min-id> <max-id>` to download graphs whose IDs are in the range from `<min-id>` to `<max-id>`,

The JSON files with the graps are downloaded into `build/graphs`.

To use a downloaded graph with ID `<id>` in Lean, use the command
```lean
load_graph <graphName> "build/graphs/<ID>"
```
This will load the graph into the variable `<graphName>`.
You can check that it loaded it with `#check <graphName>`.

### Visualization widget

Lean-HoG can visualize the imported graphs in the Lean infoview using 
[widgets](https://lean-lang.org/lean4/doc/examples/widgets.lean.html),
which work by running Javascript in the Infoview.
The visualization uses the [cytoscape.js](https://js.cytoscape.org/) javascript library.

Requirements:
* [Node.js and npm cli](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm).

To build the widgets library run
```
lake exe build_widgets
```
To use the visualization widget in a file, add the line `import LeanHog.Widgets` at the top.

Once you built the widgets, you can try them out by opening the `Examples.lean` file
and clicking on the line `#visualizeGraph Cycle7`. In the info view you should now see
something like this:
![image](https://github.com/katjabercic/Lean-HoG/assets/6967728/f4ee94ab-4d31-4192-ac80-7e35323e5c4b)

### Search the House of Graphs from Lean

You can query the House of Graphs database from within Lean via the command `#search_hog`.
To use it you have to construct a valid `hog_query` and enclose it into
`hog{ }` syntax. It has the following syntax:
```
hog_query q ::= boolean_invariant = b | numerical_invariant op x | ( q ) | q ∧ q | q ∨ q
```
where `b` is a boolean value, `x` is a numerical value
(`Int` for invariants with integral values, `Float` for invariants with continous values)
and
```
op ::= < | <= | > | >= | =
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
