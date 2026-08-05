# Rendering `Examples.lean` as a website

`Examples.lean` is meant to be read as much as run: it walks through loading graphs, deciding invariants, searching the House of Graphs from inside Lean, and finishes with a proof that traceability is not a function of the degree sequence. [Verso](https://github.com/leanprover/verso)'s *literate mode* renders it as a static site, with the Lean file staying the source of truth — the page is generated from it, not the other way round. Prose comes from `/-! ... -/` module docs and `/-- ... -/` docstrings, so narrative belongs in those rather than in `--` comments, which render as code.

This is a spike, not a finished pipeline. Two rough edges are described below and neither has been fixed in the repo.

## Building the site

`lake build Examples:literate` does not work — see [Why the search path is set by hand](#why-the-search-path-is-set-by-hand). Run this instead, from the repository root:

```sh
export PATH="/opt/homebrew/opt/cadical/bin:$PATH"    # wherever your solver lives
export LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_SRC_PATH="$PWD:$(lake env printenv LEAN_SRC_PATH)"
export DYLD_LIBRARY_PATH="$(lake env printenv DYLD_LIBRARY_PATH)"

lake build Examples
.lake/packages/verso/.lake/build/bin/verso-literate Examples .lake/build/literate/Examples.json
lake exe verso-html .lake/build/literate html
cat literate-overrides.css >> html/code.css
```

Building the page elaborates the whole file, so it needs everything `Examples.lean` needs: a SAT solver on `PATH`, Python, and network access to House of Graphs for the `#download` commands.

## Serve it over HTTP

```sh
python3 -m http.server 8765 --directory html
```

Then open <http://127.0.0.1:8765/Examples/index.html>. Do not open the file from disk: the hover layer is built inside a `fetch("-verso-docs.json")` call, which a `file://` origin blocks, so every tooltip silently fails to appear and the page gives no sign that anything is missing.

## Why the search path is set by hand

Trestle ships a directory named `Examples`, and it precedes the repository root in the source search path. Lean's `SearchPath.findWithExt` picks the first entry containing anything called `Examples`, maps it to `trestle/Examples.lean`, finds no such file, and gives up rather than continuing down the path — so our own `Examples.lean` is shadowed by a directory in a dependency, and `lake build Examples:literate` fails with `Failed to load Examples`. Putting the root first works around it. The real fix is to give the module a less generic name.

## Why the CSS override

Verso's stylesheet deliberately draws docstrings as boxed source comments, injecting the delimiters with `content: "/-!"` and `content: "-/"` on `::before` and `::after`. Combined with `width: min-content`, those three characters break across two lines, so the page shows `/-` and `!` stacked above the prose inside a rounded box. `literate-overrides.css` de-boxes module docs into ordinary page prose and removes the injected delimiters. Verso v4.29.0 adds a `docstrings_as_text` setting that does this properly, at which point the override can go.

## Known gaps

* **Command output is hover-only.** On Verso v4.28.0 the results of `#eval` and `#print axioms` are attached as tooltips rather than rendered on the page, so the site shows the commands and hides the answers. Verso v4.29.0 adds `show_output`, which renders them as visible blocks. Moving to it needs a Lean toolchain bump, which is blocked on Trestle (issue #53).
* **Proof states are collapsed.** They are click-to-expand toggles, which is how the Lean reference manual behaves, but nothing is visible until a reader opens them.
* **The graph widgets do not render.** `#show G` draws an interactive Cytoscape visualisation in the infoview, and Verso's renderer knows nothing about it, so the most distinctive output in the file is absent from the page. The repository already builds `build/js/graphVisualization.js`; mounting it in the generated HTML would be custom work rather than configuration.
* **Nothing runs this automatically.** Wiring it to CI depends on there being CI at all (issue #57), and on that CI having a solver, Python, and network access.
