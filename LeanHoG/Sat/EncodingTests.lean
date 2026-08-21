import LeanHoG.LoadGraph
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Invariant.HamiltonianCycle.SatEncoding

import Trestle.Solver.Dimacs

/-!
# Golden fixtures for the SAT encodings

Fixed expected values for the CNF that the Hamiltonian path and cycle encodings emit,
so that a change to the encoding is detected at build time. `#guard` fails elaboration
when its argument evaluates to `false`, so `lake build SatEncodingTests` is the whole
test run. It requires no SAT solver and no network, unlike `lake build Examples`.

Three properties are pinned per encoding and graph:

* `maxVar`, the number of variables;
* `size`, the number of clauses;
* the hash of `Trestle.Solver.Dimacs.formatFormula`, which is the complete DIMACS text
  and therefore also covers variable numbering, clause order and literal order.

The hash subsumes the other two. They are stated separately so that a failure reports
which of the three changed.

`maxVar` is `n * m` for a graph on `n` vertices, where `m` is the number of positions
(`n` for a path, `n + 1` for a cycle): `EncCNF.run` derives the DIMACS index of a
variable from its `IndexType` instance, which sends `Var.mk i j` to `i * m + j`.

These numbers are expected to change only when the encoding changes deliberately; when
that happens, regenerate them and note it in the commit message. `String.hash` is stable
within a toolchain but not across Lean versions, so a change to `lean-toolchain` also
requires regenerating them.

The `#eval`s at the end of the file write the formulas to `build/cnf/` for a line-by-line
`diff` between revisions. They are commented out so that an ordinary build writes nothing.
-/

namespace LeanHoG.Sat.EncodingTests

open Trestle Trestle.Encode

load_graph Path3 "examples/path3.json"
load_graph Cycle7 "examples/cycle7.json"
load_graph_from_g6 Petersen "IheA@GUAo"
load_graph G1 "examples/one.json"
load_graph_from_g6 NoVertices "?"

/-- The CNF of the Hamiltonian *path* encoding of `G`. -/
def pathCnf (G : Graph) : ICnf := EncCNF.toICnf (hamiltonianPathCNF G).val

/-- The CNF of the Hamiltonian *cycle* encoding of `G`. `h` is what the encoding needs
    to be built at all; every fixture below is nonempty, so it is `by decide`. -/
def cycleCnf (G : Graph) (h : 0 < G.vertexSize) : ICnf :=
  EncCNF.toICnf (HamiltonianCycle.hamiltonianCycleCNF G h).val

/-! ### Hamiltonian path encoding -/

-- Path3: 4 vertices, 4 positions.
#guard (pathCnf Path3).maxVar = 16
#guard (pathCnf Path3).size = 134
#guard (Solver.Dimacs.formatFormula (pathCnf Path3)).hash = 15220818186843642495

-- Cycle7: 7 vertices, 7 positions.
#guard (pathCnf Cycle7).maxVar = 49
#guard (pathCnf Cycle7).size = 812
#guard (Solver.Dimacs.formatFormula (pathCnf Cycle7)).hash = 12256336751833733215

-- Petersen: 10 vertices, 10 positions.
#guard (pathCnf Petersen).maxVar = 100
#guard (pathCnf Petersen).size = 2450
#guard (Solver.Dimacs.formatFormula (pathCnf Petersen)).hash = 4883255751730849426

/-! ### Hamiltonian cycle encoding

One more position than the path encoding at the same size: the cycle closes up by
repeating its first vertex at the last position. -/

-- Path3: 4 vertices, 5 positions.
#guard (cycleCnf Path3 (by decide)).maxVar = 20
#guard (cycleCnf Path3 (by decide)).size = 159
#guard (Solver.Dimacs.formatFormula (cycleCnf Path3 (by decide))).hash = 3829237598744941918

-- Cycle7: 7 vertices, 8 positions.
#guard (cycleCnf Cycle7 (by decide)).maxVar = 56
#guard (cycleCnf Cycle7 (by decide)).size = 892
#guard (Solver.Dimacs.formatFormula (cycleCnf Cycle7 (by decide))).hash = 16669563833796931719

-- Petersen: 10 vertices, 11 positions.
#guard (cycleCnf Petersen (by decide)).maxVar = 110
#guard (cycleCnf Petersen (by decide)).size = 2613
#guard (Solver.Dimacs.formatFormula (cycleCnf Petersen (by decide))).hash = 11179074814633449769

/-! ### The degenerate sizes

Neither is covered by the three graphs above, and both are load-bearing for the search
tactics rather than merely small.

A 0-vertex graph encodes to the *empty* CNF, which is satisfiable — that is what
`searchForHamiltonianPathAux` relies on to answer traceability at size 0 without a solver.

A 1-vertex graph's cycle CNF is unconditionally UNSAT, which is why
`hamiltonian_cycle_to_sat` and everything built on it carry `1 < G.vertexSize` rather than
`0 < G.vertexSize`. It is UNSAT only because the position loop reaches `k = 0, k' = 1`, so
`edgeConstraints` forbids vertex `0` from being adjacent to itself while the two pinning
clauses demand exactly that. Narrowing that loop — an `i < j` optimisation, say, or ranging
over `m - 1` — would silently make a 1-vertex graph satisfiable, and `#check_hamiltonian`
would then register a certificate the kernel rejects later. Hence the full text, not just
the count:

    p cnf 2 6 / 1 2 0 / 1 0 / 2 0 / -1 -2 0 / 1 0 / 2 0
-/

#guard NoVertices.vertexSize = 0
#guard (pathCnf NoVertices).size = 0

#guard G1.vertexSize = 1
#guard (cycleCnf G1 (by decide)).maxVar = 2
#guard (cycleCnf G1 (by decide)).size = 6
#guard (Solver.Dimacs.formatFormula (cycleCnf G1 (by decide))).hash = 4870943102142356345

/-! ### What the hashes cannot see

`mapProp` is `fun ⟨e, he⟩ => ⟨e, h ▸ he⟩`: it rewrites the `Prop` a `VEncCNF` is indexed by
and passes the encoding through untouched. So a `sorry` in any of the encodings' `mapProp`
obligations would emit byte-identical clauses and leave every guard above passing — while
that index is exactly what carries soundness into the solver's UNSAT branch, through
`VEncCNF.std_unsat_no_assignment`. Assert the axioms rather than printing them, so that a
`sorryAx` fails the build here instead of being discovered downstream. -/

/-- info: 'LeanHoG.hamiltonianPathCNF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanHoG.hamiltonianPathCNF

/-- info: 'LeanHoG.HamiltonianCycle.hamiltonianCycleCNF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanHoG.HamiltonianCycle.hamiltonianCycleCNF

/-! ### Diagnostics

Uncomment to dump the formulas for a line-by-line `diff` against another revision.
Left commented so that an ordinary build writes nothing. -/

-- #eval Solver.Dimacs.toFile "build/cnf/path-Path3.cnf" (pathCnf Path3)
-- #eval Solver.Dimacs.toFile "build/cnf/path-Cycle7.cnf" (pathCnf Cycle7)
-- #eval Solver.Dimacs.toFile "build/cnf/path-Petersen.cnf" (pathCnf Petersen)
-- #eval Solver.Dimacs.toFile "build/cnf/cycle-Path3.cnf" (cycleCnf Path3 (by decide))
-- #eval Solver.Dimacs.toFile "build/cnf/cycle-Cycle7.cnf" (cycleCnf Cycle7 (by decide))
-- #eval Solver.Dimacs.toFile "build/cnf/cycle-Petersen.cnf" (cycleCnf Petersen (by decide))

end LeanHoG.Sat.EncodingTests
