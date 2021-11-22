The Python code in this folder converts the [HoG data files](../data) to Lean files and
stores them to the folder `settings['output_path']` in [`convert.py`](./convert.py).

The main program is [`convert.py`](./convert.py). It is probably better not to run it directly, as we provide
a `Makefile` that will do it for you.

Run `make` in the root directory of the project to convert all graphs. 
Run `make LIMIT=n` to convert the first `n` files, i.e. `make LIMIT=5`.

## Files produced

The converter produces Lean files split into groups. 
Each group of files contains information about a number of consecutive graphs (set in `settings['graphs_per_file']`).
This group consists of the following files, each ending with the group number `#`:

* file with definitions of graphs: `{settings['db_name']}_#.lean`,
* a file for each of the invariants, named after the corresponding type class: `type_class_name_#.lean`.

Each of the graph definition files contains a structure with all the graphs in the group.
Currently, this is an array of arrays (the internal arrays have length `settings['graphs_per_line']`) named `db_#`.
Finally, the file named `{settings['db_main']}.lean` lists all the groups.

## Adding an invariant to the converter

Each `HoGGraph` has a `lean_instances` property. 
This is a dictionary with HoG invariant names as keys.
The values are templates for the corresponding Lean instance code
You can find it just under a long comment titled `INSTANCES DICTIONARY`.
The converter needs an entry for each invariant to produce the corresponding files.

It should suffice to add an entry to the dictionary.
Variables relevant for the templates are described in the `INSTANCES DICTIONARY` comment.