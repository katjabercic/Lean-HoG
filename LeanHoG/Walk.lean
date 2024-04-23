import LeanHoG.Graph
import LeanHoG.Edge
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Util.List
import Mathlib.Data.Multiset.Fintype
import Mathlib.Lean.Json

namespace LeanHoG

/-- A walk is a sequence of adjacent vertices, it may intersect itself -/
inductive Walk (G : Graph) : G.vertex → G.vertex → Type
  | here (v : G.vertex) : Walk G v v
  | step {s t u : G.vertex} : G.adjacent s t → Walk G t u →  Walk G s u

namespace Walk

def toString {G : Graph} {s t : G.vertex} : Walk G s t → String
  | here s  => s!"{s}"
  | step e w => s!"{s} -> {w.toString}"

instance walkToString {G : Graph} {s t : G.vertex} : ToString (Walk G s t) where
  toString := toString

instance reprWalk {G : Graph} {u v : G.vertex} : Repr (Walk G u v) where
  reprPrec w _ := w.toString

instance {G : Graph} {u v : G.vertex} {_ : Walk G u v} : Inhabited G.vertex where
  default := u

def isTrivial {G : Graph} {u v : G.vertex} : Walk G u v → Bool
  | here _ => true
  | step _ _ => false

def isNontrivial {G : Graph} {s t : G.vertex} : Walk G s t → Prop
  | here s => False
  | step _ _ => True

def notInWalk {G : Graph} {u v a b : G.vertex} : Walk G u v → G.adjacent a b → Bool
  | here s , e => true
  | step (t := t) _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk p e

macro p:term "↑" : term => `(reverse $p)

def edgeWalk {G : Graph} {s t : G.vertex} (e : G.adjacent s t) : Walk G s t :=
  step e (here t)

-- Definition from https://mathworld.wolfram.com/GraphPath.html
@[simp]
def length {G : Graph} {s t : G.vertex} : Walk G s t → ℕ
  | here s => 0
  | step _ p' => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {G : Graph} {s t : G.vertex} : Walk G s t → G.connected s t
  | here s => G.connected_of_eq s s (Eq.refl s)
  | step e p' => G.connected_trans _ _ _ (G.connected_of_adjacent e) (pathImpliesConnected p')

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
def vertices {G : Graph} {u v : G.vertex} : Walk G u v -> List G.vertex
  | here v => [v]
  | step conn_ut walk_tv => u :: walk_tv.vertices

@[simp] lemma vertices_len_pos {G : Graph} {u v : G.vertex} {w : Walk G u v} :
  0 < w.vertices.length := by
  induction' w
  · simp
  · simp

@[simp] lemma mem_vertices_endpoints {G : Graph} {u v : G.vertex} {w : Walk G u v} :
  u ∈ w.vertices ∧ v ∈ w.vertices := by
  induction' w with _
  · simp
  · aesop

@[simp] lemma walk_trivial_vertices_length {G : Graph} {u v : G.vertex} (p : Walk G u v)
  (h : p.isTrivial) : p.vertices.length = 1 := by
  induction' p with p ih
  · simp
  · contradiction

def verticesMultiset {G : Graph} {u v : G.vertex} :
  Walk G u v -> Multiset G.vertex := fun w => Multiset.ofList w.vertices

instance vertices_fintype {G : Graph} {u v : G.vertex} {w : Walk G u v} : Fintype w.verticesMultiset := by
  infer_instance

-- We need to provide the explicit equality of `u = v` here. Is there a nicer way to do this?
@[simp]
lemma vertices_trivial {G : Graph} {u v : G.vertex} (p : Walk G u v) (eq : u = v)
  (p_is_trivial : eq ▸ p = here u) :
  p.vertices = [u] := by
  aesop

@[simp]
lemma vertices_sublist_left {G : Graph} {u v w : G.vertex} {p : Walk G u w} {adj_u_v : G.adjacent u v}
  {q : Walk G v w} {p_is_left : p = step adj_u_v q} : p.vertices = u :: q.vertices := by
  aesop -- Can't just use simp, as it doesn't apply induction

lemma vertices_left_length {G : Graph} {u v w : G.vertex} {p : Walk G u w} {adj_u_v : G.adjacent u v}
  {q : Walk G v w} {p_is_left : p = step adj_u_v q} : q.vertices.length + 1 = p.vertices.length := by
  rw [@vertices_sublist_left G u v w p adj_u_v q p_is_left]
  simp

lemma vertices_length_as_multiset {G : Graph} {u v : G.vertex} (w : Walk G u v) :
  w.vertices.length = Fintype.card (Multiset.ofList w.vertices) := by
  simp

lemma length_as_vertices {G : Graph} {u v : G.vertex} (w : Walk G u v) :
  w.length + 1 = w.vertices.length := by
  induction' w
  · simp
  · simp; assumption -- just apply induction hypothesis

@[simp] def edges {G : Graph} {u v : G.vertex} : Walk G u v → List G.edge
  | here v => []
  | step adj_ut walk_tv =>
    let e := Graph.adjacentEdge adj_ut
    e :: walk_tv.edges

instance {G : Graph} {u v : G.vertex} : Lean.ToJson (Walk G u v) where
  toJson w := Lean.toJson w.edges

lemma edges_length {G : Graph} {u v : G.vertex} {w : Walk G u v} :
  w.edges.length = w.length := by
  induction w
  · simp
  · simp_all

@[simp]
lemma edges_sublist_left {G : Graph} {u v w : G.vertex} {p : Walk G u w} {adj_u_v : G.adjacent u v}
  {q : Walk G v w} {p_is_left : p = step adj_u_v q} :
  p.edges = G.adjacentEdge adj_u_v :: q.edges := by
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

@[simp] lemma walk_vertices_get_zero {G : Graph} [Inhabited G.vertex] {u v : G.vertex}
  (w : Walk G u v) (n : Nat) (h : n < 1) :
  w.vertices.getI n = u := by
  induction' w
  · simp_all
  · simp_all

/-- Two conescutive vertices on a path are adjacent. -/
lemma consecutive_vertices_adjacent {G : Graph} {u v : G.vertex} {w : Walk G u v}
  {i j : Fin w.vertices.length} {h : i.val + 1 = j.val} :
  G.adjacent (w.vertices.get i) (w.vertices.get j) := by
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
      have : Inhabited G.vertex := { default := u }
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

def ClosedWalk (G : Graph) (u : G.vertex) : Type := Walk G u u

namespace ClosedWalk

instance {G : Graph} {u : G.vertex} : Repr (ClosedWalk G u) where
  reprPrec c n := Walk.reprWalk.reprPrec c n

def length {G : Graph} {u : G.vertex} (w : ClosedWalk G u) : Nat :=
  Walk.length w

@[simp]
def vertices {G : Graph} {u : G.vertex} : ClosedWalk G u -> List G.vertex :=
  Walk.vertices

@[simp]
def edges {G : Graph} {u : G.vertex} : ClosedWalk G u -> List G.edge :=
  Walk.edges

instance {G : Graph} {u : G.vertex} {w : ClosedWalk G u} : Fintype w.verticesMultiset := by
  infer_instance

end ClosedWalk

/-- A walk is a path if all the vertices are distinct.
    (This implies all the edges are distinct).
-/
@[reducible]
def Walk.isPath {G : Graph} {u v : G.vertex} : Walk G u v → Bool :=
  List.all_distinct ∘ vertices

structure Path (G : Graph) (u v : G.vertex) where
  walk : Walk G u v
  isPath : walk.isPath := by rfl

namespace Path

theorem ext_iff {G : Graph} {u v : G.vertex} (p q : Path G u v) :
  p = q ↔ p.walk = q.walk := by
  rcases p with ⟨p_walk, _⟩
  rcases q with ⟨q_walk, _⟩
  simp

@[ext] theorem ext {G : Graph} (u v : G.vertex) (p q : Path G u v)
  (h : p.walk = q.walk) : p = q :=
  (ext_iff p q).mpr h

instance trivialPath {G : Graph} (u : G.vertex) : Path G u u where
  walk := .here u
  isPath := by simp [List.all_distinct]

instance {G : Graph} {u v : G.vertex} : Repr (Path G u v) where
  reprPrec p n := reprPrec p.walk n

instance {G : Graph} {u v : G.vertex} : ToString (Path G u v) where
  toString p := toString p.walk


instance {G : Graph} : Repr ((u v : G.vertex) ×' Path G u v) where
  reprPrec p n := reprPrec p.2.2 n

instance {G : Graph} {u v : G.vertex} : Lean.ToJson (Path G u v) where
  toJson p := Lean.toJson p.walk.edges

@[simp]
def vertices {G : Graph} {u v : G.vertex} : Path G u v → List G.vertex := fun p =>
  Walk.vertices p.walk

@[simp] lemma vertices_all_distinct {G : Graph} {u v : G.vertex} (p : Path G u v) :
  p.vertices.all_distinct := by
  apply p.isPath

@[simp] def edges {G : Graph} {u v : G.vertex} : Path G u v → List G.edge :=
  fun p => p.walk.edges


@[simp]
lemma subpathIsPath_left {G : Graph} {u v w : G.vertex} (p : Path G u w) (adj_u_v : G.adjacent u v)
  (q : Walk G v w) (p_is_left : p.walk = .step adj_u_v q) : q.isPath = true := by
  have walk_is_path : p.walk.isPath = true := by apply p.isPath
  aesop

/-- Two consecutive vertices on a path cannot be equal, since a path
    never repeats a vertex.
-/
lemma consecutive_vertices_distinct {G : Graph} {u v : G.vertex} {p : Path G u v}
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
def vertexSet {G : Graph} {u v : G.vertex} : Path G u v → Set G.vertex := fun p =>
  { x : G.vertex | x ∈ p.walk.vertices }

@[simp]
lemma vertexSet_finite {G : Graph} {u v : G.vertex} (p : Path G u v) :
  Set.Finite p.vertexSet :=
  List.finite_toSet p.vertices

@[simp]
def vertexMultiset {G : Graph} {u v : G.vertex} : Path G u v → Multiset G.vertex := fun p =>
  Walk.verticesMultiset p.walk

@[simp]
lemma vertexMultiset_nodup {G : Graph} {u v : G.vertex} {p : Path G u v} :
  Multiset.Nodup p.vertexMultiset := by
  apply Iff.mp Multiset.coe_nodup
  apply Iff.mp List.all_distinct_iff_nodup
  apply p.isPath

@[simp]
def vertexFinset {G : Graph} {u v : G.vertex} : Path G u v → Finset G.vertex := fun p =>
  ⟨p.vertexMultiset, vertexMultiset_nodup⟩

instance path_vertices_fintype {G : Graph} {u v : G.vertex} {w : Path G u v} : Fintype w.vertexMultiset := by
  infer_instance

lemma path_vertices_length_as_multiset {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.vertices.length = Fintype.card (Multiset.ofList p.vertices) := by
  simp

@[simp]
def length {G : Graph} {u v : G.vertex} : Path G u v → Nat
  | ⟨w, _⟩ => w.length

lemma edges_length {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.edges.length = p.length := by
  simp [Walk.edges_length]

lemma vertexMultiset_card_is_vertices_length {G : Graph} {u v : G.vertex} {p : Path G u v} :
  Multiset.card p.vertexMultiset = p.vertices.length := by
  simp
  rfl

lemma vertexFinset_card_is_vertices_length {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.vertexFinset.card = p.vertices.length := by
  simp [vertexMultiset_card_is_vertices_length]
  rfl

lemma length_is_num_vertices {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.length + 1 = p.vertexFinset.card := by
  simp [vertexFinset_card_is_vertices_length, Walk.length_as_vertices]
  rfl

lemma length_as_vertices {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.length + 1 = p.vertices.length := by
  simp [Walk.length_as_vertices]

lemma length_as_vertices_multiset {G : Graph} {u v : G.vertex} {p : Path G u v} :
  p.length + 1 = Fintype.card p.vertexMultiset := by
  simp [Walk.length_as_vertices]
  rfl

lemma length_as_fintype_card {G : Graph} {u v : G.vertex} (p : Path G u v) :
  p.length + 1 = Fintype.card (Fin (List.length (vertices p))) := by
  simp_all only [length, Walk.length_as_vertices, Graph.vertex, Graph.connected, vertices, Fintype.card_fin]

/-- The length of a path in a graph is at most the number of vertices -/
theorem maxPathLength {G : Graph} {u v : G.vertex} (p : Path G u v) :
  p.length + 1 <= Fintype.card G.vertex := by
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
theorem maxPathLength' {G : Graph} {u v : G.vertex} (p : Path G u v) :
  p.length + 1 <= Finset.card p.vertexFinset := by
  by_contra h
  rw [not_le, length_is_num_vertices] at h
  simp_all only [lt_self_iff_false]

def isShortest {G : Graph} {u v : G.vertex} (p : Path G u v) : Prop :=
  ∀ (u' v': G.vertex) (q : Path G u' v'), p.length ≤ q.length

def isShortestFromTo {G : Graph} (u v : G.vertex) (p : Path G u v) : Prop :=
  ∀ (q : Path G u v), p.length ≤ q.length

def isLongest {G : Graph} {u v : G.vertex} (p : Path G u v) : Prop :=
  ∀ (u' v' : G.vertex) (q : Path G u' v'), q.length ≤ p.length

def isLongestFromTo {G : Graph} (u v : G.vertex) (p : Path G u v) : Prop :=
  ∀ (q : Path G u v), q.length ≤ p.length

end Path

@[simp]
def ClosedWalk.isCycle {G : Graph} {u : G.vertex} : ClosedWalk G u → Bool := fun cw =>
  let vertices := cw.vertices
  let edges := cw.edges
  match vertices with
  | [] => true
  | _ :: vertices =>
    vertices.all_distinct && edges.all_distinct

structure Cycle (G : Graph) (u : G.vertex) where
  cycle : ClosedWalk G u
  isCycle : ClosedWalk.isCycle cycle

namespace Cycle

theorem ext_iff {G : Graph} {u : G.vertex} (c d : Cycle G u) :
  c = d ↔ c.cycle = d.cycle := by
  rcases c with ⟨c_cycle, _⟩
  rcases d with ⟨c_cycle, _⟩
  simp

@[ext] theorem ext {G : Graph} (u : G.vertex) (c d : Cycle G u)
  (h : c.cycle = d.cycle) : c = d :=
  (ext_iff c d).mpr h

instance {G : Graph} {u : G.vertex} : Repr (Cycle G u) where
  reprPrec p n := reprPrec p.cycle n

instance {G : Graph} : Repr ((u : G.vertex) ×' Cycle G u) where
  reprPrec p n := reprPrec p.2 n

def length {G : Graph} {u : G.vertex} (c : Cycle G u) : Nat := c.cycle.length

def edges {G : Graph} {u : G.vertex} (c : Cycle G u) := c.cycle.edges

def isShortest {G : Graph} (u : G.vertex) (c : Cycle G u) : Prop :=
  ∀ (u' : G.vertex) (c' : Cycle G u'), c.length ≤ c'.length

def isLongest {G : Graph} (u : G.vertex) (c : Cycle G u) : Prop :=
  ∀ (u' : G.vertex) (c' : Cycle G u'), c'.length ≤ c.length

def isEulerian {G : Graph} {u : G.vertex} (c : Cycle G u) : Prop :=
  ∀ (e : G.edge), e ∈ c.edges

end Cycle

class ShortestPath (G : Graph) where
  u : G.vertex
  v : G.vertex
  path : Path G u v
  isShortest : path.isShortest

class LongestPath (G : Graph) where
  u : G.vertex
  v : G.vertex
  path : Path G u v
  isLongest : path.isLongest

class ShortestCycle (G : Graph) where
  u : G.vertex
  cycle : Cycle G u
  isShortest : cycle.isShortest

class LongestCycle (G : Graph) where
  u : G.vertex
  cycle : Cycle G u
  isLongest : cycle.isLongest

/-- A graph is acyclic if it doesn't contain a cycle. -/
def Graph.isAcyclic (G : Graph) : Prop :=
  ¬ ∃ (u : G.vertex) (c : ClosedWalk G u), c.isCycle

def Graph.girth (G : Graph) [c : ShortestCycle G] : Nat := c.cycle.length

def Graph.circumference (G : Graph) [c : LongestCycle G] : Nat := c.cycle.length

def Graph.lengthOfLongestPath (G : Graph) [p : LongestPath G] : Nat := p.path.length

def Graph.distance (G : Graph) (u v : G.vertex) (p : Path G u v)
  (_ : p.isShortestFromTo u v) : Nat := p.length

def Graph.isEulerian (G : Graph) : Prop :=
  ∃ (u : G.vertex) (c : Cycle G u), c.isEulerian

def Cycle.isTriangle {G : Graph} {u : G.vertex} (c : Cycle G u) : Prop :=
  c.length = 3

end LeanHoG
