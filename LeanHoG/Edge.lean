import Lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex
import Batteries.Data.RBMap.Basic
import Batteries.Data.RBMap.Lemmas

namespace LeanHoG

structure Edge (m : Nat) where
  fst : Fin m
  snd : Fin m
  ord : fst < snd
deriving Fintype, Repr

-- Two edges are equal as soon as their endpoints are: `ord` is a proof field.
attribute [ext] Edge

instance (m : Nat) : Lean.ToJson (Edge m) where
  toJson e := Lean.Json.arr #[e.fst, e.snd]

def Edge.fromNats {m : Nat} (i j : Nat) (h₁ : i < j) (h₂ : j < m) : Edge m :=
  {
    fst := ⟨i, lt_trans h₁ h₂⟩,
    snd := ⟨j, h₂⟩,
    ord := h₁
  }

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

@[simp, reducible]
def fst_snd (m : Nat) (e : Edge m) : Lex (Fin m × Fin m) := (e.fst, e.snd)

def fst_snd_injective {m : Nat} : Function.Injective (fst_snd m) := by
  intro a b
  cases a ; cases b ; simp
  intro h ; injection h ; trivial

instance Edge.linearOrder (m : Nat) : LinearOrder (Edge m) :=
  LinearOrder.lift' (fst_snd m) fst_snd_injective

@[reducible]
def EdgeSet (n : Nat) := Batteries.RBSet (Edge n) (Edge.linearOrder n).compare

def Fin.shiftDown {n : Nat} (v : Fin n) (u : Fin n) (h : u ≠ v) : Fin (n - 1) :=
    if hlt : u < v then ⟨u, by omega⟩ else ⟨u - 1, by omega⟩

lemma Fin.shiftDown_lt_shiftDown {n : Nat} {v u w : Fin n} (hu : u ≠ v) (hw : w ≠ v) :
    u < w → Fin.shiftDown v u hu < Fin.shiftDown v w hw := by
  intro huw
  simp [Fin.shiftDown]
  grind

/-- Reindex a vertex of `G - v` as a vertex of `G`: the inverse of `Fin.shiftDown`, putting
the gap at `v` back. -/
def Fin.shiftUp {n : Nat} (v : Fin n) (u : Fin (n - 1)) : Fin n :=
  if hlt : (u : Nat) < (v : Nat) then ⟨u, by omega⟩ else ⟨u + 1, by omega⟩

/-- Both reindexings are easiest to reason about one level down, on the underlying naturals:
every lemma below is then `split_ifs <;> omega`. -/
lemma Fin.val_shiftDown {n : Nat} (v u : Fin n) (h : u ≠ v) :
    ((Fin.shiftDown v u h : Fin (n - 1)) : Nat)
      = if (u : Nat) < (v : Nat) then (u : Nat) else (u : Nat) - 1 := by
  unfold Fin.shiftDown
  split_ifs <;> first | rfl | omega

lemma Fin.val_shiftUp {n : Nat} (v : Fin n) (u : Fin (n - 1)) :
    ((Fin.shiftUp v u : Fin n) : Nat)
      = if (u : Nat) < (v : Nat) then (u : Nat) else (u : Nat) + 1 := by
  unfold Fin.shiftUp
  split_ifs <;> rfl

/-- `Fin.shiftUp v` is strictly monotone; discharges the `ord` field of `Edge.shiftUp`. -/
lemma Fin.shiftUp_lt_shiftUp {n : Nat} {v : Fin n} {u w : Fin (n - 1)} :
    u < w → Fin.shiftUp v u < Fin.shiftUp v w := by
  intro huw
  have h : (u : Nat) < (w : Nat) := huw
  rw [Fin.lt_def, Fin.val_shiftUp, Fin.val_shiftUp]
  split_ifs <;> omega

/-- The image of `Fin.shiftUp v` is exactly the vertices other than `v`. -/
lemma Fin.shiftUp_ne {n : Nat} (v : Fin n) (u : Fin (n - 1)) : Fin.shiftUp v u ≠ v := by
  apply Fin.ne_of_val_ne
  rw [Fin.val_shiftUp]
  split_ifs <;> omega

lemma Fin.shiftDown_shiftUp {n : Nat} (v : Fin n) (u : Fin (n - 1)) (h : Fin.shiftUp v u ≠ v) :
    Fin.shiftDown v (Fin.shiftUp v u) h = u := by
  apply Fin.ext
  rw [Fin.val_shiftDown, Fin.val_shiftUp]
  have := u.isLt
  split_ifs <;> omega

lemma Fin.shiftUp_shiftDown {n : Nat} (v u : Fin n) (h : u ≠ v) :
    Fin.shiftUp v (Fin.shiftDown v u h) = u := by
  have hne : (u : Nat) ≠ (v : Nat) := Fin.val_ne_of_ne h
  apply Fin.ext
  rw [Fin.val_shiftUp, Fin.val_shiftDown]
  split_ifs <;> omega

def Edge.shiftDown {m : Nat} (e : Edge m) (v : Fin m) (h : e.fst ≠ v ∧ e.snd ≠ v) :
    Edge (m - 1) :=
  ⟨Fin.shiftDown v e.fst h.1, Fin.shiftDown v e.snd h.2, Fin.shiftDown_lt_shiftDown h.1 h.2 e.ord⟩

/-- Reindex an edge of `G - v` as an edge of `G`: the inverse of `Edge.shiftDown`. -/
def Edge.shiftUp {m : Nat} (e : Edge (m - 1)) (v : Fin m) : Edge m :=
  ⟨Fin.shiftUp v e.fst, Fin.shiftUp v e.snd, Fin.shiftUp_lt_shiftUp e.ord⟩

/-- Edges in the image of `shiftUp` never meet `v`, so they are exactly the edges `shiftDown`
accepts. -/
lemma Edge.shiftUp_ne {m : Nat} (e : Edge (m - 1)) (v : Fin m) :
    (e.shiftUp v).fst ≠ v ∧ (e.shiftUp v).snd ≠ v :=
  ⟨Fin.shiftUp_ne v e.fst, Fin.shiftUp_ne v e.snd⟩

lemma Edge.shiftDown_shiftUp {m : Nat} (e : Edge (m - 1)) (v : Fin m)
    (h : (e.shiftUp v).fst ≠ v ∧ (e.shiftUp v).snd ≠ v) :
    (e.shiftUp v).shiftDown v h = e := by
  apply Edge.ext
  · exact Fin.shiftDown_shiftUp v e.fst h.1
  · exact Fin.shiftDown_shiftUp v e.snd h.2

lemma Edge.shiftUp_shiftDown {m : Nat} (e : Edge m) (v : Fin m)
    (h : e.fst ≠ v ∧ e.snd ≠ v) : (e.shiftDown v h).shiftUp v = e := by
  apply Edge.ext
  · exact Fin.shiftUp_shiftDown v e.fst h.1
  · exact Fin.shiftUp_shiftDown v e.snd h.2

/-- `shiftDown` and `shiftUp` are mutually inverse bijections between the edges of `G` missing
`v` and the edges of `G - v`. This is the form the fold invariant below rewrites with. -/
lemma Edge.shiftDown_eq_iff {m : Nat} (e : Edge m) (e' : Edge (m - 1)) (v : Fin m)
    (h : e.fst ≠ v ∧ e.snd ≠ v) : e.shiftDown v h = e' ↔ e = e'.shiftUp v := by
  constructor
  · intro heq
    rw [← heq, Edge.shiftUp_shiftDown]
  · intro heq
    subst heq
    exact Edge.shiftDown_shiftUp e' v h

/-- An edge meeting `v` is never in the image of `shiftUp`; this is the dropped-edge case of the
fold invariant. -/
lemma Edge.ne_shiftUp_of_mem {m : Nat} (e : Edge m) (e' : Edge (m - 1)) (v : Fin m)
    (h : ¬(e.fst ≠ v ∧ e.snd ≠ v)) : e'.shiftUp v ≠ e := by
  intro heq
  apply h
  rw [← heq]
  exact Edge.shiftUp_ne e' v

/-- One step of `EdgeSet.deleteConnections`'s fold: keep an edge, reindexed, unless it meets `v`.
Named rather than inlined so the fold invariant below can be stated. -/
def EdgeSet.deleteStep {n : Nat} (v : Fin n) (acc : EdgeSet (n - 1)) (e : Edge n) :
    EdgeSet (n - 1) :=
  if h : e.fst ≠ v ∧ e.snd ≠ v then
    acc.insert (e.shiftDown v h)
  else
    acc

def EdgeSet.deleteConnections {n : Nat} (es : EdgeSet n) (v : Fin n) : EdgeSet (n - 1) :=
  es.foldl (init := ∅) (EdgeSet.deleteStep v)

/-! ### Membership in an `EdgeSet`

`Batteries.RBSet` membership is stated up to the comparator, `x ∈ t ↔ ∃ y ∈ t.toList, cmp x y = .eq`.
Since `Edge.linearOrder` is a `LinearOrder.lift'` along an injective map, `.eq` collapses to
propositional equality, and membership is just list membership. -/

lemma EdgeSet.mem_iff_mem_toList {n : Nat} {e : Edge n} {es : EdgeSet n} :
    e ∈ es ↔ e ∈ es.toList := by
  rw [Batteries.RBSet.mem_iff_mem_toList]
  constructor
  · rintro ⟨f, hf, hcmp⟩
    rw [compare_eq_iff_eq] at hcmp
    exact hcmp ▸ hf
  · intro h
    exact ⟨e, h, by rw [compare_eq_iff_eq]⟩

lemma EdgeSet.not_mem_empty {n : Nat} (e : Edge n) : e ∉ (∅ : EdgeSet n) := by
  intro h
  rw [EdgeSet.mem_iff_mem_toList] at h
  rw [show (∅ : EdgeSet n).toList = [] from rfl] at h
  simp at h

lemma EdgeSet.mem_insert_iff {n : Nat} {es : EdgeSet n} {e e' : Edge n} :
    e' ∈ es.insert e ↔ e' ∈ es ∨ e' = e := by
  constructor
  · intro h
    rw [EdgeSet.mem_iff_mem_toList, Batteries.RBSet.mem_toList_insert] at h
    rcases h with ⟨h, -⟩ | h
    · exact Or.inl (EdgeSet.mem_iff_mem_toList.mpr h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Batteries.RBSet.mem_insert_of_mem e h
    · subst h
      exact Batteries.RBSet.mem_insert_self e' es

/-! ### Correctness of `deleteConnections` -/

/-- The invariant of `deleteConnections`'s fold, generalized over the accumulator so that the
inductive hypothesis applies at `deleteStep v acc e` and not just at `acc`. Every edge of the
result either was already accumulated or is the reindexing of an edge still to be seen — and by
`Edge.shiftDown_eq_iff` the latter is witnessed by `e.shiftUp v` itself, so no existential is
needed. -/
lemma EdgeSet.mem_foldl_deleteStep {n : Nat} (v : Fin n) (l : List (Edge n))
    (acc : EdgeSet (n - 1)) (e : Edge (n - 1)) :
    e ∈ l.foldl (EdgeSet.deleteStep v) acc ↔ e ∈ acc ∨ e.shiftUp v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons f l ih =>
    rw [List.foldl_cons, ih, List.mem_cons]
    unfold EdgeSet.deleteStep
    split_ifs with h
    · rw [EdgeSet.mem_insert_iff, eq_comm (a := e), Edge.shiftDown_eq_iff f e v h, eq_comm (a := f)]
      tauto
    · have hne : e.shiftUp v ≠ f := Edge.ne_shiftUp_of_mem f e v h
      tauto

/-- `deleteConnections` computes the edge set of the induced subgraph on the vertices other than
`v`: an edge of `G - v` is present exactly when the edge it comes from is present in `G`.

Stated via `Edge.shiftUp` rather than an existential over edges of `G`, which makes it directly
usable as a rewrite; `mem_deleteConnections` below is the existential form. -/
theorem EdgeSet.mem_deleteConnections' {n : Nat} (es : EdgeSet n) (v : Fin n) (e : Edge (n - 1)) :
    e ∈ es.deleteConnections v ↔ e.shiftUp v ∈ es := by
  have hfold : es.foldl (init := (∅ : EdgeSet (n - 1))) (EdgeSet.deleteStep v)
      = es.toList.foldl (EdgeSet.deleteStep v) ∅ := Batteries.RBNode.foldl_eq_foldl_toList
  unfold EdgeSet.deleteConnections
  rw [hfold, EdgeSet.mem_foldl_deleteStep, ← EdgeSet.mem_iff_mem_toList]
  simp [EdgeSet.not_mem_empty]

theorem EdgeSet.mem_deleteConnections {n : Nat} (es : EdgeSet n) (v : Fin n)
  (e : Edge (n - 1)) :
    e ∈ es.deleteConnections v ↔
      ∃ (f : Edge n) (h : f.fst ≠ v ∧ f.snd ≠ v), f ∈ es ∧ f.shiftDown v h = e
  := by
  rw [EdgeSet.mem_deleteConnections']
  constructor
  · intro h
    exact ⟨e.shiftUp v, Edge.shiftUp_ne e v, h, Edge.shiftDown_shiftUp e v _⟩
  · rintro ⟨f, hf, hmem, heq⟩
    rw [Edge.shiftDown_eq_iff] at heq
    exact heq ▸ hmem

end LeanHoG
