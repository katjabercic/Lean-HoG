import Trestle.Model.PropFun
import Trestle.Encode.VEncCNF

/-!
# An `n × m` Boolean grid and the CNF constraints on it

The Hamiltonian path and cycle encodings are the same encoding: an `n × m` grid of Boolean
variables, `n` rows by `m` columns, asking that each row occupy exactly one column, each column
hold exactly one row, and that the rows of consecutive columns be related. Rows are the vertices
of a graph and columns are positions along a walk. The path takes `m = n`; the cycle takes
`m = n + 1`, because its last position repeats its first, and that one difference is the source
of everything else that distinguishes them — the exemption in `rowAmoOn` and the two fixed cells.

Nothing here mentions `Graph`: adjacency arrives as a relation parameter. That is the point. This
file's only job is to own the variable numbering and the clause emission order, and it cannot own
them if it also has opinions about graphs.

**Everything here is byte-visible.** The emitted DIMACS depends on the field order of `Var`, the
nesting order of the `for_all` towers, the order of the literals inside each `addClause`, and the
order of `seq` arms — and on nothing else, since `mapProp` passes the encoding through untouched.
`LeanHoG/Sat/EncodingTests.lean` hashes the full DIMACS text of six fixtures, so a change to any
of those four things will move a hash there.

Two conventions worth keeping, both of which are what let the atoms be stated once for any `n`
and `m`: this file contains **no `Fin` literals** — every index is a bound variable or a
parameter, so nothing needs `NeZero m` — and **no size hypotheses**: every atom is total at
`n = 0` and `m = 0`, where `Array.finRange 0 = #[]` emits nothing and the `∀` is vacuous.
-/

namespace LeanHoG.Sat.Grid

open Trestle Encode VEncCNF Model PropFun LitVar

/-- `Var n m` is "row `i` occupies column `j`" of an `n × m` Boolean grid.

**The field order is load-bearing.** `EncCNF.run` derives the DIMACS numbering solely from the
`IndexType` instance. The derived instance for a two-field structure goes through the
`(_ : Fin n) × Fin m` proxy that `proxy_equiv%` builds out of the *fields*, and then through
`Fin.pair x y = x * n_right + y` (`Trestle/Upstream/IndexType.lean:33`), so `toFin ⟨i, j⟩` is
`i * m + j`. Putting the column first would give `j * n + i`, and adding a third field would
multiply every index out. Either renumbers every emitted CNF. -/
structure Var (n m : Nat) where
  row : Fin n
  col : Fin m
deriving DecidableEq, IndexType

/- The numbering this file rests on, pinned at the point of definition so that a change to the
   structure fails here rather than two commits later as an unexplained fixture hash. The DIMACS
   index of `Var.mk i j` is `i * m + j + 1`; `EncCNF.run` contributes the `+ 1` via the 1-based
   `IVar.ofIndex`. The last two cases are the two shapes this library instantiates: `m = n` for a
   path and `m = n + 1` for a cycle. -/
#guard IndexType.card (Var 4 5) = 20
#guard (IndexType.toFin (Var.mk (2 : Fin 4) (3 : Fin 5))).val = 2 * 5 + 3
#guard (IndexType.toFin (Var.mk (2 : Fin 10) (7 : Fin 10))).val = 2 * 10 + 7
#guard (IndexType.toFin (Var.mk (2 : Fin 10) (7 : Fin 11))).val = 2 * 11 + 7

/-- A `Unit`-valued verified encoding over an `n × m` grid. -/
abbrev VCnf (n m : Nat) := VEncCNF (Var n m) Unit

/-- Row `i` occupies column `j`. -/
@[simp] def cell {n m : Nat} (i : Fin n) (j : Fin m) : PropFun (Var n m) :=
  Var.mk i j

/-! ## The atoms

Each atom is a `@[simp]` `PropPred` paired with a builder that emits its clauses, and **each
builder carries its own `mapProp`**. Keeping one `mapProp` per atom is what keeps the obligations
easy: each is an equality of two `∀`-skeletons with the same binder structure, where a predicate
parameter sits symmetrically on both sides and `simp` never has to evaluate it. A single `mapProp`
over a whole bundle would have to relate a conjunction to a `seq`-of-`for_all` skeleton all at
once.

The `@[simp]` attributes are not decoration. Both `Correctness.lean` files reduce a goal about an
atom down to `τ ⊨ …` form by `simp` alone, so quietly removing one stops those proofs working.
The literal-list helpers below are deliberately *not* `@[simp]`: they are emission plumbing that
no correctness proof should want unfolded, so they are named in the local `simp` call instead of
being pushed into the global set.
-/

/-! ### Every row occupies some column -/

@[simp] def rowNonempty (n m : Nat) : PropPred (Var n m) := fun τ =>
  ∀ (i : Fin n), ∃ (j : Fin m), τ ⊨ cell i j

/-- "Row `i` occupies column `j`", for each `j`, columns ascending. -/
def rowLits (n m : Nat) (i : Fin n) : List (Literal <| Var n m) :=
  List.finRange m |>.map (mkPos <| Var.mk i ·)

def rowNonemptyClauses (n m : Nat) : VCnf n m (rowNonempty n m) :=
  ( for_all (Array.finRange n) fun i =>
      addClause (List.toArray (rowLits n m i)) )
  |> mapProp (by
    ext τ
    simp [rowLits, Clause.toPropFun, Array.finRange]
  )

/-! ### Every column holds some row -/

@[simp] def colNonempty (n m : Nat) : PropPred (Var n m) := fun τ =>
  ∀ (j : Fin m), ∃ (i : Fin n), τ ⊨ cell i j

/-- "Row `i` occupies column `j`", for each `i`, rows ascending. -/
def colLits (n m : Nat) (j : Fin m) : List (Literal <| Var n m) :=
  List.finRange n |>.map (mkPos <| Var.mk · j)

def colNonemptyClauses (n m : Nat) : VCnf n m (colNonempty n m) :=
  ( for_all (Array.finRange m) fun j =>
      addClause (List.toArray (colLits n m j)) )
  |> mapProp (by
    ext τ
    simp [colLits, Clause.toPropFun, Array.finRange]
  )

/-! ### No row occupies two columns -/

/-- No row occupies two distinct columns that both satisfy `p`.

`p` exists for the cycle, which must exempt column `0`: its first and last columns are the same
position on the cycle, and so legitimately hold the same row. A path exempts nothing and uses
`rowAmo` below rather than passing a vacuous `p` here. -/
@[simp] def rowAmoOn (n m : Nat) (p : Fin m → Prop) : PropPred (Var n m) := fun τ =>
  ∀ (i : Fin n), ∀ (j k : Fin m), j ≠ k ∧ p j ∧ p k → τ ⊨ (cell i j)ᶜ ⊔ (cell i k)ᶜ

/-- The pairwise at-most-one clauses, one per (row, ordered pair of distinct columns). Both
orderings of a pair are emitted, which is redundant but is what this encoding has always done;
Trestle's `Encode/Cardinality` `amoPairwise` emits only `i < j` and so would change the CNF. -/
def rowAmoOnClauses (n m : Nat) (p : Fin m → Prop) [DecidablePred p] :
    VCnf n m (rowAmoOn n m p) :=
  ( for_all (Array.finRange n) fun i =>
    for_all (Array.finRange m) fun j =>
    for_all (Array.finRange m) fun k =>
      VEncCNF.guard (j ≠ k ∧ p j ∧ p k) fun _ =>
        addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk i k]) )
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

/-- No row occupies two distinct columns. -/
@[simp] def rowAmo (n m : Nat) : PropPred (Var n m) := fun τ =>
  ∀ (i : Fin n), ∀ (j k : Fin m), j ≠ k → τ ⊨ (cell i j)ᶜ ⊔ (cell i k)ᶜ

/-- `rowAmoOn` with a vacuous side condition, restated without it.

`mapProp` is `fun ⟨e, he⟩ => ⟨e, h ▸ he⟩`: it passes the encoding through untouched and can only
change the statement. So this emits exactly the clauses `rowAmoOnClauses n m (fun _ => True)`
emits — the guard `j ≠ k ∧ True ∧ True` decides exactly as `j ≠ k` does — while stating the
constraint without the two vacuous antecedents. Stating it that way is what keeps the path's
constraint *syntactically* what it was before this encoding was factored, so its correctness
proof cannot tell the difference and no simp lemma has to fire in the right order. -/
def rowAmoClauses (n m : Nat) : VCnf n m (rowAmo n m) :=
  rowAmoOnClauses n m (fun _ => True)
  |> mapProp (by
    ext τ
    simp
  )

/-! ### No column holds two rows -/

/-- No column holds two distinct rows.

Unparameterized, unlike `rowAmoOn`: both encodings want exactly this, with no exemption. An
opaque relation here would also break the cycle's proof, which discharges this goal by feeding an
`i = k` to a hypothesis of the form `i ≠ k`. -/
@[simp] def colAmo (n m : Nat) : PropPred (Var n m) := fun τ =>
  ∀ (j : Fin m), ∀ (i k : Fin n), i ≠ k → τ ⊨ (cell i j)ᶜ ⊔ (cell k j)ᶜ

def colAmoClauses (n m : Nat) : VCnf n m (colAmo n m) :=
  ( for_all (Array.finRange m) fun j =>
    for_all (Array.finRange n) fun i =>
    for_all (Array.finRange n) fun k =>
      VEncCNF.guard (i ≠ k) fun _ =>
        addClause (#[mkNeg <| Var.mk i j, mkNeg <| Var.mk k j]) )
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

/-! ### The rows of consecutive columns are related -/

/-- The row in column `k` and the row in the next column are `R`-related.

Stated in the contrapositive, which is what a clause can say: two rows that are *not* `R`-related
cannot sit in consecutive columns. Both encodings instantiate `R := G.adjacent`.

"Consecutive" is fixed rather than a parameter, and should stay that way. Both encodings mean
`k + 1`, so a parameter buys nothing, and it is load-bearing for the *proofs*: the path's
`τ_edge` closes with `simp [hk]` against a hypothesis literally shaped `k.val + 1 = k'.val`, and
an opaque relation would leave that step nothing to match.

Note also that it must be spelled on `.val`. `(· + 1 = ·)` on `Fin m` is modular, so it would
relate the last column to the first — turning a path encoding into a cycle one, which adds
clauses and makes `hamiltonian_path_to_sat` false rather than merely slow. -/
@[simp] def consecutiveRelated (n m : Nat) (R : Fin n → Fin n → Prop) :
    PropPred (Var n m) := fun τ =>
  ∀ (k k' : Fin m), k.val + 1 = k'.val →
    ∀ (i j : Fin n), ¬ R i j →
      τ ⊨ (cell i k)ᶜ ⊔ (cell j k')ᶜ

/-- The two guards stay nested rather than combined, and the column pair stays the *outer* loop:
the emitted clause order is column-pair-major, so flattening the towers or hoisting a guard would
reorder the CNF even though it would not change the set of clauses. -/
def consecutiveRelatedClauses (n m : Nat) (R : Fin n → Fin n → Prop) [DecidableRel R] :
    VCnf n m (consecutiveRelated n m R) :=
  ( for_all (Array.finRange m) fun k =>
    for_all (Array.finRange m) fun k' =>
      VEncCNF.guard (k.val + 1 = k'.val) fun _ =>
        for_all (Array.finRange n) fun i =>
        for_all (Array.finRange n) fun j =>
          VEncCNF.guard (¬ R i j) fun _ =>
            addClause (#[mkNeg <| Var.mk i k, mkNeg <| Var.mk j k']) )
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun, Array.finRange]
  )

/-! ### A fixed cell -/

/-- Row `i` occupies column `j`.

Used only by the cycle, to fix vertex `0` in the first and last columns — a WLOG that shrinks the
search space, since a Hamiltonian cycle passes through every vertex anyway. It is one cell rather
than a list of them so that a caller pinning two cells writes a literal conjunction, which is
what lets the cycle's correctness proof go on splitting it with `constructor`.

Keeping it here, thin as it is, buys one invariant worth having: `Var.mk` now appears only in this
file and in the two solver-readback loops. Its argument order is what the `IndexType` numbering
reads, so confining it to the file that `#guard`s that numbering is the point. -/
@[simp] def pin (n m : Nat) (i : Fin n) (j : Fin m) : PropPred (Var n m) := fun τ =>
  τ ⊨ cell i j

def pinClauses (n m : Nat) (i : Fin n) (j : Fin m) : VCnf n m (pin n m i j) :=
  addClause (#[mkPos <| Var.mk i j])
  |> mapProp (by
    ext τ
    simp [Clause.toPropFun]
  )

end LeanHoG.Sat.Grid
