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
