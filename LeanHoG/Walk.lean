import LeanHoG.Graph
import LeanHoG.Edge
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Util.List
import Mathlib.Data.Multiset.Fintype
import Mathlib.Lean.Json

namespace LeanHoG

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Walk (g : Graph) : g.vertex → g.vertex → Type
  | trivial (v : g.vertex) : Walk g v v
  | left {s t u : g.vertex} : g.adjacent s t → Walk g t u →  Walk g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Walk.left $u $v _ $walk (by rfl))
macro " ⬝ " u:term : term => `(Walk.trivial $u)

namespace Walk

def toString {g : Graph} {s t : g.vertex} : Walk g s t → String
  | .trivial s  => s!"{s}"
  | .left e w => s!"{s} -> {w.toString}"

instance walkToString {g : Graph} {s t : g.vertex} : ToString (Walk g s t) where
  toString := fun w => w.toString

instance reprWalk {g : Graph} {u v : g.vertex} : Repr (Walk g u v) where
  reprPrec w _ := w.toString

instance {g : Graph} {u v : g.vertex} {_ : Walk g u v} : Inhabited g.vertex where
  default := u

def isTrivial {g : Graph} {u v : g.vertex} : Walk g u v → Bool
  | .trivial _ => true
  | .left _ _ => false

def isNontrivial {g : Graph} {s t : g.vertex} : Walk g s t → Prop
  | .trivial s => False
  | .left _ _ => True

def notInWalk {g : Graph} {u v a b : g.vertex} : Walk g u v → g.adjacent a b → Bool
  | .trivial s , e => true
  | .left (t := t) _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk p e

macro p:term "↑" : term => `(reverse $p)

def edgeWalk {g : Graph} {s t : g.vertex} (e : g.adjacent s t) : Walk g s t :=
  left e (trivial t)

-- Definition from https://mathworld.wolfram.com/GraphPath.html
@[simp]
def length {g : Graph} {s t : g.vertex} : Walk g s t → ℕ
  | .trivial s => 0
  | .left _ p' => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : Graph} {s t : g.vertex} : Walk g s t → g.connected s t
  | .trivial s => g.connected_of_eq s s (Eq.refl s)
  | .left e p' => g.connected_trans _ _ _ (g.connected_of_adjacent e) (pathImpliesConnected p')

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

@[simp]
def vertices {g : Graph} {u v : g.vertex} : Walk g u v -> List g.vertex
  | .trivial v => [v]
  | .left conn_ut walk_tv => u :: walk_tv.vertices

@[simp] lemma vertices_len_pos {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  0 < w.vertices.length := by
  induction' w
  · simp
  · simp

@[simp] lemma mem_vertices_endpoints {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  u ∈ w.vertices ∧ v ∈ w.vertices := by
  induction' w with _
  · simp
  · aesop

@[simp] lemma walk_trivial_vertices_length {g : Graph} {u v : g.vertex} (p : Walk g u v)
  (h : p.isTrivial) : p.vertices.length = 1 := by
  induction' p with p ih
  · simp
  · contradiction

def verticesMultiset {g : Graph} {u v : g.vertex} :
  Walk g u v -> Multiset g.vertex := fun w => Multiset.ofList w.vertices

instance vertices_fintype {g : Graph} {u v : g.vertex} {w : Walk g u v} : Fintype w.verticesMultiset := by
  infer_instance

-- We need to provide the explicit equality of `u = v` here. Is there a nicer way to do this?
@[simp]
lemma vertices_trivial {g : Graph} {u v : g.vertex} (p : Walk g u v) (eq : u = v)
  (p_is_trivial : eq ▸ p = trivial u) :
  p.vertices = [u] := by
  aesop

@[simp]
lemma vertices_sublist_left {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_u_v : g.adjacent u v}
  {q : Walk g v w} {p_is_left : p = left adj_u_v q} : p.vertices = u :: q.vertices := by
  aesop -- Can't just use simp, as it doesn't apply induction

lemma vertices_left_length {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_u_v : g.adjacent u v}
  {q : Walk g v w} {p_is_left : p = left adj_u_v q} : q.vertices.length + 1 = p.vertices.length := by
  rw [@vertices_sublist_left g u v w p adj_u_v q p_is_left]
  simp

lemma vertices_length_as_multiset {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.vertices.length = Fintype.card (Multiset.ofList w.vertices) := by
  simp

lemma length_as_vertices {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.length + 1 = w.vertices.length := by
  induction' w
  · simp
  · simp; assumption -- just apply induction hypothesis

@[simp] def edges {g : Graph} {u v : g.vertex} : Walk g u v → List g.edge
  | .trivial v => []
  | .left adj_ut walk_tv =>
    let e := Graph.adjacentEdge adj_ut
    e :: walk_tv.edges

instance {g : Graph} {u v : g.vertex} : Lean.ToJson (Walk g u v) where
  toJson w := Lean.toJson w.edges

lemma edges_length {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  w.edges.length = w.length := by
  induction w
  · simp
  · simp_all

@[simp]
lemma edges_sublist_left {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_u_v : g.adjacent u v}
  {q : Walk g v w} {p_is_left : p = left adj_u_v q} :
  p.edges = g.adjacentEdge adj_u_v :: q.edges := by
  aesop

lemma lt_lt_succ_lt {a b n : Nat} (h : a < b) (h' : b < Nat.succ n) : a < n := by
  by_contra h
  simp at h
  apply Iff.mp Nat.le_iff_lt_or_eq at h
  cases h with
  | inl H =>
    linarith
  | inr H =>
    linarith

lemma succ_consecutive_exists_cast {n : Nat} (i j : Fin (Nat.succ n)) (h : i.val = j.val + 1) :
  ∃ k : Fin n, Fin.castSucc k = j := by
  apply Iff.mpr Fin.exists_iff
  apply Exists.intro j.val
  have h' : j.val < i.val := by
    linarith
  have h : ↑j < n := by
    apply lt_lt_succ_lt h' i.isLt
  apply Exists.intro h
  simp

@[simp] lemma walk_vertices_get_zero {g : Graph} [Inhabited g.vertex] {u v : g.vertex}
  (w : Walk g u v) (n : Nat) (h : n < 1) :
  w.vertices.getI n = u := by
  induction' w
  · simp_all
  · simp_all

/-- Two conescutive vertices on a path are adjacent. -/
lemma consecutive_vertices_adjacent {g : Graph} {u v : g.vertex} {w : Walk g u v}
  {i j : Fin w.vertices.length} {h : i.val + 1 = j.val} :
  g.adjacent (w.vertices.get i) (w.vertices.get j) := by
  have i_lt_j : i < j := by
    apply Iff.mpr Fin.lt_iff_val_lt_val
    rw [← h]
    apply Nat.lt_succ_self
  induction' w with _ s t r adj walk ih
  · simp_all
  · simp at i j
    have h' := Fin.eq_zero_or_eq_succ i
    cases' h' with h' h'
    · simp [h']
      have j_neq_0 : j ≠ 0 := by
        by_contra h''
        rw [h', h''] at i_lt_j
        contradiction
      let ⟨j', cond'⟩ := Fin.eq_succ_of_ne_zero j_neq_0
      rw [cond']
      simp
      have : Inhabited g.vertex := { default := u }
      rw [← List.getI_eq_get]
      rw [walk_vertices_get_zero walk]
      exact adj
      simp_all
    · let ⟨k, cond⟩ := h'
      simp [cond]
      have h' := Fin.eq_zero_or_eq_succ j
      cases' h' with h' h'
      · rw [h'] at i_lt_j
        contradiction
      · let ⟨l, cond'⟩ := h'
        simp [cond']
        have k_l : k.val + 1 = l.val := by
          simp_all
        have k_lt_l : k < l := by
          apply Iff.mpr Fin.lt_iff_val_lt_val
          rw [← k_l]
          apply Nat.lt_succ_self
        have adj_k_l := @ih k l k_l k_lt_l
        exact adj_k_l

end Walk

def ClosedWalk (g : Graph) (u : g.vertex) : Type := Walk g u u

namespace ClosedWalk

instance {g : Graph} {u : g.vertex} : Repr (ClosedWalk g u) where
  reprPrec c n := Walk.reprWalk.reprPrec c n

def length {g : Graph} {u : g.vertex} (w : ClosedWalk g u) : Nat :=
  Walk.length w

@[simp]
def vertices {g : Graph} {u : g.vertex} : ClosedWalk g u -> List g.vertex :=
  Walk.vertices

@[simp]
def edges {g : Graph} {u : g.vertex} : ClosedWalk g u -> List g.edge :=
  Walk.edges

instance {g : Graph} {u : g.vertex} {w : ClosedWalk g u} : Fintype w.verticesMultiset := by
  infer_instance

end ClosedWalk

/-- A walk is a path if all the vertices are distinct.
    (This implies all the edges are distinct).
-/
@[simp] def Walk.isPath {g : Graph} {u v : g.vertex} : Walk g u v → Bool :=
  List.all_distinct ∘ vertices

structure Path (g : Graph) (u v : g.vertex) where
  walk : Walk g u v
  isPath : walk.isPath = true := by rfl

namespace Path

theorem ext_iff {g : Graph} {u v : g.vertex} (p q : Path g u v) :
  p = q ↔ p.walk = q.walk := by
  rcases p with ⟨p_walk, _⟩
  rcases q with ⟨q_walk, _⟩
  simp

@[ext] theorem ext {g : Graph} (u v : g.vertex) (p q : Path g u v)
  (h : p.walk = q.walk) : p = q :=
  (ext_iff p q).mpr h

instance trivialPath {g : Graph} (u : g.vertex) : Path g u u where
  walk := Walk.trivial u
  isPath := by simp [List.all_distinct]

instance {g : Graph} {u v : g.vertex} : Repr (Path g u v) where
  reprPrec p n := reprPrec p.walk n

instance {g : Graph} {u v : g.vertex} : ToString (Path g u v) where
  toString p := toString p.walk


instance {g : Graph} : Repr ((u v : g.vertex) ×' Path g u v) where
  reprPrec p n := reprPrec p.2.2 n

instance {g : Graph} {u v : g.vertex} : Lean.ToJson (Path g u v) where
  toJson p := Lean.toJson p.walk.edges

@[simp]
def vertices {g : Graph} {u v : g.vertex} : Path g u v → List g.vertex := fun p =>
  Walk.vertices p.walk

@[simp] lemma vertices_all_distinct {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.vertices.all_distinct := by
  apply p.isPath

@[simp] def edges {g : Graph} {u v : g.vertex} : Path g u v → List g.edge :=
  fun p => p.walk.edges


@[simp]
lemma subpathIsPath_left {g : Graph} {u v w : g.vertex} (p : Path g u w) (adj_u_v : g.adjacent u v)
  (q : Walk g v w) (p_is_left : p.walk = Walk.left adj_u_v q) : q.isPath = true := by
  simp
  have walk_is_path : p.walk.isPath = true := by apply p.isPath
  aesop

/-- Two consecutive vertices on a path cannot be equal, since a path
    never repeats a vertex.
-/
lemma consecutive_vertices_distinct {g : Graph} {u v : g.vertex} {p : Path g u v}
  {i j : Fin p.vertices.length} {h : i.val + 1 = j.val} :
  p.vertices.get i ≠ p.vertices.get j := by
  have dist : p.vertices.all_distinct := by
    apply p.isPath
  have i_neq_j : i ≠ j := by
    by_contra h'
    rw [h'] at h
    apply Nat.succ_ne_self at h
    exact h
  by_contra h
  have : i = j := by apply List.all_distinct_get_inj p.vertices dist i j h
  contradiction

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
  apply Iff.mp List.all_distinct_iff_nodup
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

lemma edges_length {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.edges.length = p.length := by
  simp [Walk.edges_length]

lemma vertexMultiset_card_is_vertices_length {g : Graph} {u v : g.vertex} {p : Path g u v} :
  Multiset.card p.vertexMultiset = p.vertices.length := by
  simp
  rfl

lemma vertexFinset_card_is_vertices_length {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.vertexFinset.card = p.vertices.length := by
  simp [vertexMultiset_card_is_vertices_length]
  rfl

lemma length_is_num_vertices {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.length + 1 = p.vertexFinset.card := by
  simp [vertexFinset_card_is_vertices_length, Walk.length_as_vertices]
  rfl

lemma length_as_vertices {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.length + 1 = p.vertices.length := by
  simp [Walk.length_as_vertices]

lemma length_as_vertices_multiset {g : Graph} {u v : g.vertex} {p : Path g u v} :
  p.length + 1 = Fintype.card p.vertexMultiset := by
  simp [Walk.length_as_vertices]
  rfl

lemma length_as_fintype_card {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 = Fintype.card (Fin (List.length (vertices p))) := by
  simp_all only [length, Walk.length_as_vertices, Graph.vertex, Graph.connected, vertices, Fintype.card_fin]

/-- The length of a path in a graph is at most the number of vertices -/
theorem maxPathLength {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 <= Fintype.card g.vertex := by
  by_contra h
  -- We want to apply the pigeonhole principle to show we must have a vertex appearing twice on the path.
  -- So we're going to use `Fintype.exists_ne_map_eq_of_card_lt` (the pigeonhole principle).
  -- Before that we have to rewrite h into a form we can use
  rw [not_le, length_as_fintype_card] at h
  have := Fintype.exists_ne_map_eq_of_card_lt p.vertices.get h
  match this with
  | ⟨i, j, i_neq_j, i_get_eq_j_get⟩ =>
    have i_eq_j := by apply List.all_distinct_get_inj p.vertices p.isPath i j i_get_eq_j_get
    contradiction

-- Same theorem just different proof
theorem maxPathLength' {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.length + 1 <= Finset.card p.vertexFinset := by
  by_contra h
  rw [not_le, length_is_num_vertices] at h
  simp_all only [lt_self_iff_false]

def isShortest {g : Graph} {u v : g.vertex} (p : Path g u v) : Prop :=
  ∀ (u' v': g.vertex) (q : Path g u' v'), p.length ≤ q.length

def isShortestFromTo {g : Graph} (u v : g.vertex) (p : Path g u v) : Prop :=
  ∀ (q : Path g u v), p.length ≤ q.length

def isLongest {g : Graph} {u v : g.vertex} (p : Path g u v) : Prop :=
  ∀ (u' v' : g.vertex) (q : Path g u' v'), q.length ≤ p.length

def isLongestFromTo {g : Graph} (u v : g.vertex) (p : Path g u v) : Prop :=
  ∀ (q : Path g u v), q.length ≤ p.length

end Path

@[simp]
def ClosedWalk.isCycle {g : Graph} {u : g.vertex} : ClosedWalk g u → Bool := fun cw =>
  let vertices := cw.vertices
  let edges := cw.edges
  match vertices with
  | [] => true
  | _ :: vertices =>
    vertices.all_distinct && edges.all_distinct

structure Cycle (g : Graph) (u : g.vertex) where
  cycle : ClosedWalk g u
  isCycle : ClosedWalk.isCycle cycle

namespace Cycle

theorem ext_iff {g : Graph} {u : g.vertex} (c d : Cycle g u) :
  c = d ↔ c.cycle = d.cycle := by
  rcases c with ⟨c_cycle, _⟩
  rcases d with ⟨c_cycle, _⟩
  simp

@[ext] theorem ext {g : Graph} (u : g.vertex) (c d : Cycle g u)
  (h : c.cycle = d.cycle) : c = d :=
  (ext_iff c d).mpr h

instance {g : Graph} {u : g.vertex} : Repr (Cycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex) ×' Cycle g u) where
  reprPrec p n := reprPrec p.2 n

def length {g : Graph} {u : g.vertex} (c : Cycle g u) : Nat := c.cycle.length

def edges {g : Graph} {u : g.vertex} (c : Cycle g u) := c.cycle.edges

def isShortest {g : Graph} (u : g.vertex) (c : Cycle g u) : Prop :=
  ∀ (u' : g.vertex) (c' : Cycle g u'), c.length ≤ c'.length

def isLongest {g : Graph} (u : g.vertex) (c : Cycle g u) : Prop :=
  ∀ (u' : g.vertex) (c' : Cycle g u'), c'.length ≤ c.length

def isEulerian {g : Graph} {u : g.vertex} (c : Cycle g u) : Prop :=
  ∀ (e : g.edge), e ∈ c.edges

end Cycle

class ShortestPath (g : Graph) where
  u : g.vertex
  v : g.vertex
  path : Path g u v
  isShortest : path.isShortest

class LongestPath (g : Graph) where
  u : g.vertex
  v : g.vertex
  path : Path g u v
  isLongest : path.isLongest

class ShortestCycle (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  isShortest : cycle.isShortest

class LongestCycle (g : Graph) where
  u : g.vertex
  cycle : Cycle g u
  isLongest : cycle.isLongest

/-- A graph is acyclic if it doesn't contain a cycle. -/
def Graph.isAcyclic (g : Graph) : Prop :=
  ¬ ∃ (u : g.vertex) (c : ClosedWalk g u), c.isCycle

def Graph.girth (g : Graph) [c : ShortestCycle g] : Nat := c.cycle.length

def Graph.circumference (g : Graph) [c : LongestCycle g] : Nat := c.cycle.length

def Graph.lengthOfLongestPath (g : Graph) [p : LongestPath g] : Nat := p.path.length

def Graph.distance (g : Graph) (u v : g.vertex) (p : Path g u v)
  (_ : p.isShortestFromTo u v) : Nat := p.length

def Graph.isEulerian (g : Graph) : Prop :=
  ∃ (u : g.vertex) (c : Cycle g u), c.isEulerian

def Cycle.isTriangle {g : Graph} {u : g.vertex} (c : Cycle g u) : Prop :=
  c.length = 3

def Graph.allPaths (g : Graph) := { p : (u v : g.vertex) ×' Path g u v | true }

def Graph.allPathsFromTo (g : Graph) (u v : g.vertex) := { p : Path g u v | true }

end LeanHoG
