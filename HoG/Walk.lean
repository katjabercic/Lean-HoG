import Mathlib.Tactic.LibrarySearch
import HoG.Graph
import HoG.Invariant.ConnectedComponents
import HoG.TreeSet

namespace HoG

-- -- [ ] Be able to define the functions on paths my pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Walk (g : Graph) : g.vertex → g.vertex → Type
  | trivial (v : g.vertex) : Walk g v v
  | left {s t u : g.vertex} : g.connected s t → Walk g t u →  Walk g s u
  | right {s t u : g.vertex} : Walk g s t → g.connected t u → Walk g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro walk:term " ~- " "{" u:term "," v:term "}" : term => `(Walk.right _ $u $v (by rfl) $walk)
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Walk.left $u $v _ $walk (by rfl))
macro " ⬝ " u:term : term => `(Walk.trivial $u)

def Walk.toString {g : Graph} {s t : g.vertex} : Walk g s t → String
  | .trivial s  => s!"{s}"
  | .left e w => s!"{s} -> {w.toString}"
  | .right w e => s!"{w.toString} -> {t}"

instance walkToString {g : Graph} {s t : g.vertex} : ToString (Walk g s t) where
  toString := fun w => w.toString

instance reprWalk {g : Graph} {u v : g.vertex} : Repr (Walk g u v) where
  reprPrec w _ := w.toString

def Walk.isNontrivial {g : Graph} {s t : g.vertex} : Walk g s t → Prop
  | .trivial s => False
  | .left _ _ => True
  | .right _ _ => True

def Walk.notInWalk {g : Graph} {u v a b : g.vertex} : Walk g u v → g.adjacent a b → Bool
  | .trivial s , e => true
  | .left (t := t) _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk p e
  | .right (t := t) p _, e => (a != t || b != v) && (a != v  || b != t) && notInWalk p e

def Walk.reverse {g : Graph} {s t : g.vertex} :  Walk g s t → Walk g t s
  | .trivial s => .trivial s
  | .left e p => Walk.right (reverse p) (g.connectedSymm _ _ e)
  | .right p e => Walk.left (g.connectedSymm _ _ e) (reverse p)

macro p:term "↑" : term => `(Walk.reverse $p)

def Walk.concat {g : Graph} {s t u : g.vertex} : Walk g s t → Walk g t u → Walk g s u := fun p q =>
  match p with
  | .trivial s => q
  | .left e p' =>
    match q with
    | .trivial t => Walk.left e p'
    | .left r q' => Walk.left e (concat (Walk.right p' r) q')
    | .right q' r => Walk.left e (Walk.right (concat p' q') r)
  | p' =>
    match q with
    | .trivial t => p'
    | .left r q' => concat (Walk.right p' r) q'
    | .right q' r => Walk.right (concat p' q') r

-- macro p:term "++" q:term : term => `(Walk.concat $p $q)

def Walk.edgeWalk {g : Graph} {s t : g.vertex} (e : g.connected s t) : Walk g s t :=
  Walk.left e (Walk.trivial t)

-- Definition from https://mathworld.wolfram.com/GraphPath.html
@[simp]
def Walk.length {g : Graph} {s t : g.vertex} : Walk g s t → ℕ
  | .trivial s => 0
  | .left _ p' => length p' + 1
  | .right p' _ => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : Graph} {s t : g.vertex} : Walk g s t → g.connected s t
  | .trivial s => g.connectedEq s s (Eq.refl s)
  | .left e p' => g.connectedTrans _ _ _ e (pathImpliesConnected p')
  | .right p' e => g.connectedTrans _ _ _ (pathImpliesConnected p') e

theorem strongInduction
  (α : Type)
  (f : α → ℕ) (P : α → Type)
  (step : ∀ a, (∀ b, f b < f a → P b) → P a) :
  ∀ a, P a := by
  intro a
  let Q := fun n => ∀ a, f a = n → P a
  have Qstep : ∀ (n : ℕ), (∀ (m : ℕ), m < n → Q m) → Q n
  { intros n h a ξ
    apply (step a)
    intros b fb_lt_fa
    rw [ξ] at fb_lt_fa
    apply (h (f b)) fb_lt_fa
    rfl
  }
  exact @WellFounded.fix _ Q Nat.lt Nat.lt_wfRel.wf Qstep (f a) a rfl

-- lemma witnessWalkToRoot (g : Graph) (w : ComponentsCertificate g) (s : g.vertex) :
  -- Walk g s (w.root (w.component s)) := by
  -- apply @strongInduction g.vertex (w.distToRoot) (fun v => Walk g v (w.root (w.component v)))
  -- { intros v h
    -- by_cases H : (0 < w.distToRoot v)
    -- · let u := w.next v
      -- let hyp := w.distZeroRoot v H
      -- have p : Walk w.G u (w.root (w.c u)) := by apply h; cases hyp; assumption
      -- have same_c : w.c ↑u = w.c ↑v := by
        -- have er : edgeRelation w.G ↑u ↑v := by simp [hyp]
        -- apply ltByCases u v
        -- · intro H'
          -- let e : Edge := Edge.mk (u, v)
          -- apply w.connectEdges e (edgeRelationIsMem er)
        -- · intro H'
          -- rw [H']
        -- · intro H'
          -- let e : Edge := Edge.mk (v, u)
          -- have er' : edgeRelation w.G ↑v ↑u := by apply edgeRelationSymmetric er
          -- apply Eq.symm
          -- apply w.connectEdges e (edgeRelationIsMem er')
      -- rw [←same_c]
      -- have q : Walk w.G u v := by apply Walk.edgeWalk; cases hyp; assumption
      -- exact (q ↑) + p
    -- · simp at H
      -- have h := w.uniquenessOfRoots v H
      -- rw [←h]
      -- apply Walk.trivial
      -- sorry -- apply v.isLt
  -- }

def ClosedWalk (g : Graph) (u : g.vertex) : Type := Walk g u u

instance {g : Graph} {u : g.vertex} : Repr (ClosedWalk g u) where
  reprPrec c n := reprWalk.reprPrec c n

def ClosedWalk.length {g : Graph} {u : g.vertex} (w : ClosedWalk g u) : Nat :=
  Walk.length w

@[simp]
def Walk.vertices {g : Graph} {u v : g.vertex} : Walk g u v -> List g.vertex
  | .trivial v => [v]
  | .left conn_ut walk_tv => u :: walk_tv.vertices
  | .right walk_ut conn_tv => v :: walk_ut.vertices

def Walk.verticesMultiset {g : Graph} {u v : g.vertex} :
  Walk g u v -> Multiset g.vertex := fun w => Multiset.ofList w.vertices

instance walk_vertices_fintype {g : Graph} {u v : g.vertex} {w : Walk g u v} : Fintype w.verticesMultiset := by
  infer_instance

-- We need to provide the explicit equality of `u = v` here. Is there a nicer way to do this?
@[simp]
lemma walk_vertices_trivial {g : Graph} {u v : g.vertex} (p : Walk g u v) (eq : u = v)
  (p_is_trivial : eq ▸ p = Walk.trivial u) :
  p.vertices = [u] := by
  aesop

@[simp]
lemma walk_vertices_sublist_left {g : Graph} {u v w : g.vertex} (p : Walk g u w) (conn_u_v : g.connected u v)
  (q : Walk g v w) (p_is_left : p = Walk.left conn_u_v q) : p.vertices = u :: q.vertices := by
  aesop -- Can't just use simp, as it doesn't apply induction

@[simp]
lemma walk_vertices_sublist_right {g : Graph} {u v w : g.vertex} (p : Walk g u w) (conn_v_w : g.connected v w)
  (q : Walk g u v) (p_is_right : p = Walk.right q conn_v_w) : p.vertices = w :: q.vertices := by
  aesop  -- Can't just use simp, as it doesn't apply induction

lemma walk_vertices_length_as_multiset {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.vertices.length = Fintype.card (Multiset.ofList w.vertices) := by
  simp

@[simp]
lemma walkLengthAsVertices {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.length + 1 = w.vertices.length := by
  induction' w
  · simp
  · simp; assumption -- just apply induction hypothesis
  · simp; assumption -- just apply induction hypothesis

@[simp]
def ClosedWalk.vertices {g : Graph} {u : g.vertex} : ClosedWalk g u -> List g.vertex :=
  Walk.vertices

instance {g : Graph} {u : g.vertex} {w : ClosedWalk g u} : Fintype w.verticesMultiset := by
  infer_instance

end HoG

@[simp]
def List.all_distinct {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => x ∉ xs && xs.all_distinct

lemma all_distinct_nodup {α : Type} [DecidableEq α] {l : List α} :
  l.all_distinct = true ↔ l.Nodup := by
  induction' l
  repeat simp_all

lemma all_distinct_dedup {α : Type} [DecidableEq α] (l : List α) :
  l.all_distinct = true ↔ List.dedup l = l := by
  simp only [all_distinct_nodup, List.dedup_eq_self]

lemma index_of_lt_length_of_exists {α : Type} [DecidableEq α] (xs : List α)
  (_ : xs.all_distinct) (x : α) (h : x ∈ xs) :
  xs.indexOf x < xs.length := by
  apply List.findIdx_lt_length_of_exists
  apply Exists.intro x
  apply And.intro
  exact h
  simp

-- TODO: Surely we can just apply the theorem we used to prove this instead of a separate lemma
lemma get_implies_get? {α : Type} (l : List α) (i j : Fin l.length) :
  (l.get i) = (l.get j) → l.get? i = l.get? j := by
  simp [List.get?_eq_get]

/--
  Reformulation of injectivity of get for a list with the `all_distinct` property.
-/
lemma all_distinct_ne_idx {α : Type} [DecidableEq α] (l : List α) (d : l.all_distinct = true) :
  (∀ (i j : Fin l.length), l.get i = l.get j → i = j) := by
  have d' : l.Nodup := Iff.mp all_distinct_nodup d
  intros i j h
  let h' : l.get? i = l.get? j := get_implies_get? l i j h
  have := List.get?_inj i.2 d' h'
  apply Fin.ext this -- have to apply Fin extensionality

namespace HoG

@[simp]
def Walk.isPath {g : Graph} {u v : g.vertex} : Walk g u v → Bool :=
  List.all_distinct ∘ vertices

class Path (g : Graph) (u v : g.vertex) where
  walk : Walk g u v
  isPath : walk.isPath = true

namespace Path

instance trivialPath {g : Graph} (u : g.vertex) : Path g u u where
  walk := Walk.trivial u
  isPath := by simp [List.all_distinct]

instance {g : Graph} {u v : g.vertex} : Repr (Path g u v) where
  reprPrec p n := reprPrec p.walk n

instance {g : Graph} : Repr ((u v : g.vertex) ×' Path g u v) where
  reprPrec p n := reprPrec p.2.2 n

@[simp]
def vertices {g : Graph} {u v : g.vertex} : Path g u v → List g.vertex := fun p =>
  Walk.vertices p.walk

@[simp]
def vertexSet {g : Graph} {u v : g.vertex} : Path g u v → Set g.vertex := fun p =>
  { x : g.vertex | x ∈ p.walk.vertices }

@[simp]
lemma vertexSet_finite {g : Graph} {u v : g.vertex} (p : Path g u v) :
  Set.Finite p.vertexSet :=
  List.finite_toSet p.vertices

@[simp]
def vertexMultiset {g : Graph} {u v : g.vertex} : Path g u v → Multiset g.vertex := fun p =>
  Walk.verticesMultiset p.walk

@[simp]
lemma vertexMultiset_nodup {g : Graph} {u v : g.vertex} {p : Path g u v} :
  Multiset.Nodup p.vertexMultiset := by
  apply Iff.mp Multiset.coe_nodup
  apply Iff.mp all_distinct_nodup
  apply p.isPath

@[simp]
def vertexFinset {g : Graph} {u v : g.vertex} : Path g u v → Finset g.vertex := fun p =>
  ⟨p.vertexMultiset, vertexMultiset_nodup⟩

instance path_vertices_fintype {g : Graph} {u v : g.vertex} {w : Path g u v} : Fintype w.vertexMultiset := by
  infer_instance

lemma path_vertices_length_as_multiset {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.vertices.length = Fintype.card (Multiset.ofList p.vertices) := by
  simp

@[simp]
def length {g : Graph} {u v : g.vertex} : Path g u v → Nat
  | ⟨w, _⟩ => w.length

@[simp]
lemma subpathIsPath_left {g : Graph} {u v w : g.vertex} (p : Path g u w) (conn_u_v : g.connected u v)
  (q : Walk g v w) (p_is_left : p.walk = Walk.left conn_u_v q) : q.isPath = true := by
  simp
  have walk_is_path : walk.isPath = true := by apply p.isPath
  aesop

@[simp]
lemma subpathIsPath_right {g : Graph} {u v w : g.vertex} (p : Path g u w) (conn_v_w : g.connected v w)
  (q : Walk g u v) (p_is_right : p.walk = Walk.right q conn_v_w) : q.isPath = true := by
  simp
  have walk_is_path : walk.isPath = true := by apply p.isPath
  aesop

lemma vertexMultiset_card_is_vertices_length {g : Graph} {u v : g.vertex} {p : Path g u v} :
  Multiset.card p.vertexMultiset = p.vertices.length := by
  simp
  rfl

lemma vertexFinset_card_is_vertices_length {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.vertices.length = p.vertexFinset.card := by
  simp [vertexMultiset_card_is_vertices_length]
  rfl

lemma path_length_is_num_vertices {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.length + 1 = p.vertexFinset.card := by
  simp [vertexFinset_card_is_vertices_length]
  rfl

lemma path_length_as_vertices {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 = p.vertices.length := by
  simp

lemma path_length_as_vertices_multiset {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 = Fintype.card p.vertexMultiset := by
  aesop

lemma path_length_as_fintype_card {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 = Fintype.card (Fin (List.length (vertices p))) := by
  simp_all only [length, walkLengthAsVertices, Graph.vertex, Graph.connected, vertices, Fintype.card_fin]

/-- The length of a path in a graph is at most the number of vertices -/
theorem maxPathLength {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 <= Fintype.card g.vertex := by
  by_contra h
  -- We want to apply the pigeonhole principle to show we must have a vertex appearing twice on the path
  -- So we're going to use `Fintype.exists_ne_map_eq_of_card_lt`
  -- Before that we have to rewrite h into a form we can use
  rw [not_le, path_length_as_fintype_card] at h
  have := Fintype.exists_ne_map_eq_of_card_lt p.vertices.get h
  match this with
  | ⟨i, j, i_neq_j, i_get_eq_j_get⟩ =>
    have i_eq_j := by apply all_distinct_ne_idx p.vertices p.isPath i j i_get_eq_j_get
    contradiction

-- Same theorem just different proof
theorem maxPathLength' {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 <= Finset.card p.vertexFinset := by
  by_contra h
  rw [not_le, path_length_is_num_vertices] at h
  simp_all only [lt_self_iff_false]

end Path

@[simp]
def ClosedWalk.isCycle {g : Graph} {u : g.vertex} : ClosedWalk g u → Bool := fun cw =>
  let vertices := Walk.vertices cw
  match vertices with
  | [] => true
  | _ :: vs =>
    List.all_distinct vs

class Cycle (g : Graph) (u : g.vertex) where
  cycle : ClosedWalk g u
  isCycle : ClosedWalk.isCycle cycle

instance {g : Graph} {u : g.vertex} : Repr (Cycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex) ×' Cycle g u) where
  reprPrec p n := reprPrec p.2 n

end HoG
