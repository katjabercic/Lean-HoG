import HoG.Graph
import HoG.Invariant.ConnectedComponents
import HoG.SetTree
import HoG.Util.List

namespace HoG

-- [ ] Be able to define the functions on paths by pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Walk (g : Graph) : g.vertex → g.vertex → Type
  | trivial (v : g.vertex) : Walk g v v
  | left {s t u : g.vertex} : g.adjacent s t → Walk g t u →  Walk g s u
  | right {s t u : g.vertex} : Walk g s t → g.adjacent t u → Walk g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro walk:term " ~- " "{" u:term "," v:term "}" : term => `(Walk.right _ $u $v (by rfl) $walk)
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Walk.left $u $v _ $walk (by rfl))
macro " ⬝ " u:term : term => `(Walk.trivial $u)

namespace Walk

def toString {g : Graph} {s t : g.vertex} : Walk g s t → String
  | .trivial s  => s!"{s}"
  | .left e w => s!"{s} -> {w.toString}"
  | .right w e => s!"{w.toString} -> {t}"

instance walkToString {g : Graph} {s t : g.vertex} : ToString (Walk g s t) where
  toString := fun w => w.toString

instance reprWalk {g : Graph} {u v : g.vertex} : Repr (Walk g u v) where
  reprPrec w _ := w.toString

def isTrivial {g : Graph} {u v : g.vertex} : Walk g u v → Bool
  | .trivial _ => true
  | .left _ _ => false
  | .right _ _ => false

lemma isTrivial_vertex {g : Graph} {u v : g.vertex} (p : Walk g u v)
  (h : p.isTrivial = true) :
  (w : g.vertex) ×' (eq₁ : w = u) ×' (eq₂ : w = v) ×' (p = (eq₁ ▸ eq₂ ▸ trivial w)) := by
  sorry

def isNontrivial {g : Graph} {s t : g.vertex} : Walk g s t → Prop
  | .trivial s => False
  | .left _ _ => True
  | .right _ _ => True

def notInWalk {g : Graph} {u v a b : g.vertex} : Walk g u v → g.adjacent a b → Bool
  | .trivial s , e => true
  | .left (t := t) _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk p e
  | .right (t := t) p _, e => (a != t || b != v) && (a != v  || b != t) && notInWalk p e

def reverse {g : Graph} {s t : g.vertex} :  Walk g s t → Walk g t s
  | .trivial s => .trivial s
  | .left e p => right (reverse p) (g.symmetricAdjacent _ _ e)
  | .right p e => left (g.symmetricAdjacent _ _ e) (reverse p)

macro p:term "↑" : term => `(reverse $p)

def concat {g : Graph} {s t u : g.vertex} : Walk g s t → Walk g t u → Walk g s u := fun p q =>
  match p with
  | .trivial s => q
  | .left e p' =>
    match q with
    | .trivial t => left e p'
    | .left r q' => left e (concat (right p' r) q')
    | .right q' r => left e (right (concat p' q') r)
  | p' =>
    match q with
    | .trivial t => p'
    | .left r q' => concat (right p' r) q'
    | .right q' r => right (concat p' q') r

-- macro p:term "++" q:term : term => `(concat $p $q)

def edgeWalk {g : Graph} {s t : g.vertex} (e : g.adjacent s t) : Walk g s t :=
  left e (trivial t)

-- Definition from https://mathworld.wolfram.com/GraphPath.html
@[simp]
def length {g : Graph} {s t : g.vertex} : Walk g s t → ℕ
  | .trivial s => 0
  | .left _ p' => length p' + 1
  | .right p' _ => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : Graph} {s t : g.vertex} : Walk g s t → g.connected s t
  | .trivial s => g.connectedEq s s (Eq.refl s)
  | .left e p' => g.connectedTrans _ _ _ (g.adjacentConnected e) (pathImpliesConnected p')
  | .right p' e => g.connectedTrans _ _ _ (pathImpliesConnected p') (g.adjacentConnected e)

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
  | .right walk_ut conn_tv => v :: walk_ut.vertices

@[simp] lemma walk_trivial_vertices_length {g : Graph} {u v : g.vertex} (p : Walk g u v)
  (h : p.isTrivial) : p.vertices.length = 1 := by
  induction' p with p ih
  · simp
  · contradiction
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

lemma walk_vertices_left_get {g : Graph} {u v w : g.vertex} (p : Walk g u w) (adj_u_v : g.adjacent u v)
  (q : Walk g v w) (p_is_left : p = left adj_u_v q) (i : Fin q.vertices.length) :
  q.vertices.get i = p.vertices.get (Fin.cast (@vertices_left_length g u v w p adj_u_v q p_is_left) (Fin.castSucc i)) := by
  have := @vertices_sublist_left g u v w p adj_u_v q p_is_left
  sorry

@[simp]
lemma vertices_sublist_right {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_v_w : g.adjacent v w}
  {q : Walk g u v} {p_is_right : p = right q adj_v_w} : p.vertices = w :: q.vertices := by
  aesop  -- Can't just use simp, as it doesn't apply induction

lemma vertices_right_length {g : Graph} {u v w : g.vertex} (p : Walk g u w) (adj_v_w : g.adjacent v w)
  (q : Walk g u v) (p_is_right : p = right q adj_v_w)  : p.vertices.length = q.vertices.length + 1 := by
  rw [@vertices_sublist_right g u v w p adj_v_w q p_is_right]
  simp

lemma vertices_length_as_multiset {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.vertices.length = Fintype.card (Multiset.ofList w.vertices) := by
  simp

lemma length_as_vertices {g : Graph} {u v : g.vertex} (w : Walk g u v) :
  w.length + 1 = w.vertices.length := by
  induction' w
  · simp
  · simp; assumption -- just apply induction hypothesis
  · simp; assumption -- just apply induction hypothesis

@[simp] def edges {g : Graph} {u v : g.vertex} : Walk g u v → List g.edge
  | .trivial v => []
  | .left adj_ut walk_tv =>
    let e := Graph.adjacentEdge adj_ut
    e :: walk_tv.edges
  | .right walk_ut adj_tv =>
    let e := Graph.adjacentEdge adj_tv
    walk_ut.edges ++ [e]

lemma edges_length {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  w.edges.length = w.length := by
  induction w
  · simp
  · simp_all
  · simp_all

@[simp]
lemma edges_sublist_left {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_u_v : g.adjacent u v}
  {q : Walk g v w} {p_is_left : p = left adj_u_v q} :
  p.edges = g.adjacentEdge adj_u_v :: q.edges := by
  aesop

@[simp]
lemma edges_sublist_right {g : Graph} {u v w : g.vertex} {p : Walk g u w} {adj_v_w : g.adjacent v w}
  {q : Walk g u v} {p_is_right : p = right q adj_v_w} :
  p.edges = q.edges ++ [g.adjacentEdge adj_v_w] := by
  aesop

-- lemma foo {g : Graph} {u v w : g.vertex} {p : Walk g u v} {adj_u_v : g.adjacent u v}
--   {q : Walk g v p} {p_is_left : p = left adj_u_v q} (e : )

lemma edges_in_edges {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  ∀ e ∈ w.edges, g.edgeTree.mem e.val := by
  intro e e_in_et
  have ⟨_, cond⟩ := e
  apply cond

@[simp] def moo {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  Fin w.edges.length → Fin w.vertices.length := fun i => by
  rw [← Walk.length_as_vertices]
  rw [← Walk.edges_length]
  exact Fin.castSucc i

lemma edge_first_is_vertex {g : Graph} {u v : g.vertex} {w : Walk g u v}
  (i : Fin w.edges.length) :
  (w.edges.get i).val.fst = w.vertices.get (moo i) := by
  induction' w with _ x x' x'' adj walk ih
  · simp at i
    have := Fin.pos i
    contradiction
  · simp at i
    have := Fin.eq_castSucc_or_eq_last i
    have foo := Fin.eq_zero_or_eq_succ i
    cases this with
    | inl h =>
      cases foo with
      | inl h' =>
        let ⟨j, cond⟩ := h
        have := ih j
        rw [h'] at cond
        rw [h']
        sorry
      | inr h' => sorry
    | inr h => sorry
  sorry

@[simp] def boo {g : Graph} {u v : g.vertex} {w : Walk g u v} :
  Fin (w.edges.length + 1) → Fin w.vertices.length := fun i => by
  rw [← Walk.length_as_vertices]
  rw [← Walk.edges_length]
  exact i

lemma edge_second_is_vertex {g : Graph} {u v : g.vertex} {w : Walk g u v}
  (i : Fin w.edges.length) :
  (w.edges.get i).val.snd = w.vertices.get (boo (Fin.succ i)) := by
  induction' w with _ x x' x'' adj walk ih
  · simp at i
    have := Fin.pos i
    contradiction
  · simp at i
    have := Fin.eq_castSucc_or_eq_last i
    have foo := Fin.eq_zero_or_eq_succ i
    cases this with
    | inl h =>
      cases foo with
      | inl h' =>
        let ⟨j, cond⟩ := h
        have := ih j
        rw [h'] at cond
        rw [h']
        sorry
      | inr h' => sorry
    | inr h => sorry
  sorry

/-- Two conescutive vertices on a path are adjacent. -/
lemma consecutive_vertices_adjacent {g : Graph} {u v : g.vertex} {w : Walk g u v}
  {i j : Fin w.vertices.length} {h : i.val + 1 = j.val}  :
  g.adjacent (w.vertices.get i) (w.vertices.get j) := by
  have i_lt_j : i < j := by
    apply Iff.mpr Fin.lt_iff_val_lt_val
    rw [← h]
    apply Nat.lt_succ_self
  simp [Graph.adjacent, Graph.badjacent]
  let u := w.vertices.get i
  let v := w.vertices.get j
  apply ltByCases (w.vertices.get i) (w.vertices.get j)
  · intro h'
    simp [ltByCases, h']
  sorry
  sorry

end Walk

def ClosedWalk (g : Graph) (u : g.vertex) : Type := Walk g u u

instance {g : Graph} {u : g.vertex} : Repr (ClosedWalk g u) where
  reprPrec c n := Walk.reprWalk.reprPrec c n

def Closedlength {g : Graph} {u : g.vertex} (w : ClosedWalk g u) : Nat :=
  Walk.length w

@[simp]
def ClosedWalk.vertices {g : Graph} {u : g.vertex} : ClosedWalk g u -> List g.vertex :=
  Walk.vertices

@[simp]
def ClosedWalk.edges {g : Graph} {u : g.vertex} : ClosedWalk g u -> List (Edge g.vertexSize) :=
  Walk.edges

instance {g : Graph} {u : g.vertex} {w : ClosedWalk g u} : Fintype w.verticesMultiset := by
  infer_instance


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

@[simp] def edges {g : Graph} {u v : g.vertex} : Path g u v → List (Edge g.vertexSize) :=
  fun p => p.walk.edges

@[simp] lemma vertices_all_distinct {g : Graph} {u v : g.vertex} (p : Path g u v) :
  p.vertices.all_distinct := by
  apply p.isPath

@[simp]
lemma subpathIsPath_left {g : Graph} {u v w : g.vertex} (p : Path g u w) (adj_u_v : g.adjacent u v)
  (q : Walk g v w) (p_is_left : p.walk = Walk.left adj_u_v q) : q.isPath = true := by
  simp
  have walk_is_path : walk.isPath = true := by apply p.isPath
  aesop

@[simp]
lemma subpathIsPath_right {g : Graph} {u v w : g.vertex} (p : Path g u w) (adj_v_w : g.adjacent v w)
  (q : Walk g u v) (p_is_right : p.walk = Walk.right q adj_v_w) : q.isPath = true := by
  simp
  have walk_is_path : walk.isPath = true := by apply p.isPath
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

@[simp] def firsts {g : Graph} {u v : g.vertex} (p : Path g u v) := p.edges.map Edge.fst
@[simp] def seconds {g : Graph} {u v : g.vertex} (p : Path g u v) := p.edges.map Edge.snd

end Path

@[simp]
def ClosedWalk.isCycle {g : Graph} {u : g.vertex} : ClosedWalk g u → Bool := fun cw =>
  let vertices := cw.vertices
  let edges := cw.edges
  match vertices with
  | [] => true
  | _ :: vertices =>
    vertices.all_distinct && edges.all_distinct

class Cycle (g : Graph) (u : g.vertex) where
  cycle : ClosedWalk g u
  isCycle : ClosedWalk.isCycle cycle

instance {g : Graph} {u : g.vertex} : Repr (Cycle g u) where
  reprPrec p n := reprPrec p.cycle n

instance {g : Graph} : Repr ((u : g.vertex) ×' Cycle g u) where
  reprPrec p n := reprPrec p.2 n

end HoG
