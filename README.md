# Lean-HoG

A library for computational graph theory in [Lean 4](https://leanprover.github.io), with emphasis on verification of large datasets of graphs, an in particular the [House of Graphs](http://hog.grinvin.org/) into .

## Installation

Install Lean 4 by following [these instructions](https://leanprover-community.github.io/get_started.html). 
When successful, you should have the exectables `elan` (for installing and updating versions of Lean), `lean` itself, and `lake` (the Lean build system).

## Usage

Before compiling and using the package, run these commands in the present folder:

* `elan update` to make sure you have an up-to-date version of Lean
* `lake exe cache get` to get a cached version of Mathlib (or else wait for it to compile)

Lean 4 is best used in interactive mode using the [Visual Studio Code](https://code.visualstudio.com) editor, please consult the Lean documentation.
Once you set it up, simply open the file [`Examples.lean`](Examples.lean), which should trigger compilation.

Alternatively, build the project from the command line:

* `lake build` to compile the Lean files
* `lake clean` to remove the compiled Lean files

### Downloading graphs

To download graphs from the [House of Graphs](https://houseofgraphs.org/) (HoG) website and import them into Lean
you're going to need:
* [Pyhton](https://www.python.org/).
* The [requests](https://pypi.org/project/requests/) pyhton library.
    Once you have python installed you can get it with the command `pip install requests`.

The graphs in the HoG database are stored with corresponding ids.

To download a single graphs you can run:
* `lake exe get_graphs <ID>`

To download multiple graphs you can run:
* `lake exe get_graphs <ID1> <ID2>`
which will download all the graphs with ids in the range between `ID1` and `ID2`.

To load the downloaded graphs in a Lean file, use the command
* `load_graph <graphName> "build/graphs/<ID>"`.

This will load the graph into the variable `graphName`.
You can check that it loaded it with
* `#check graphName`.

### Visualization widget

The library has support for visualizing the imported graphs right in the Lean infoview.
This is achieved using [widgets](https://lean-lang.org/lean4/doc/examples/widgets.lean.html).
The widgets work by running javascript in the infoview.
The visualization is done using the [cytoscape.js](https://js.cytoscape.org/) javascript library.

Requirements:
* Node.js and npm cli. You can find install instructions [here](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm).

To build the widgets library run the command
* `lake exe build_widgets`

To use the visualization widget in a file you have to add the import `import LeanHog.Widgets`.

Once you built the widgets, you can try them out by opening the `Examples.lean` file
and clicking on the line `#visualizeGraph Cycle7`. In the info view you should now see
something like this:
![image](https://github.com/katjabercic/Lean-HoG/assets/6967728/f4ee94ab-4d31-4192-ac80-7e35323e5c4b)

### Search HoG database from Lean

You can query the houseofgraphs.org database from within Lean via the `#search_hog`
command. To use it you have to construct a valid `hog_query` and enclose it into
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
The list of available invariants can be found at https://houseofgraphs.org/help#invariants.
The naming convention here is that the invariants are writted using [lower camel case](https://en.wikipedia.org/wiki/Camel_case).

#### Example

```
#search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }
```

Should display in the infoview:

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

with links pointing to the houseofgraphs page for each graph.
The graphs are also available in Lean, which you can check with e.g.
```lean
#check hog_302
```
