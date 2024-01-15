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

instance {g : Graph} {u v : g.vertex} : Repr (Walk g u v) where
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

def ClosedWalk.length {g : Graph} {u : g.vertex} (w : ClosedWalk g u) : Nat :=
  Walk.length w

def Walk.vertices {g : Graph} {u v : g.vertex} : Walk g u v -> List g.vertex
  | .trivial v => [v]
  | .left conn_ut walk_tv => u :: walk_tv.vertices
  | .right walk_ut conn_tv => v :: walk_ut.vertices

def ClosedWalk.vertices {g : Graph} {u : g.vertex} : ClosedWalk g u -> List g.vertex :=
  Walk.vertices

end HoG

def List.all_distinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && xs.all_distinct

namespace HoG

@[simp]
def Walk.isPath {g : Graph} {u v : g.vertex} : Walk g u v → Bool :=
  List.all_distinct ∘ vertices

class Path (g : Graph) (u v : g.vertex) where
  walk : Walk g u v
  is_path : walk.isPath = true

instance trivialPath {g : Graph} (u : g.vertex) : Path g u u where
  walk := Walk.trivial u
  is_path := by simp [List.all_distinct]

instance {g : Graph} {u v : g.vertex} : Repr (Path g u v) where
  reprPrec p n := reprPrec p.walk n

instance {g : Graph} : Repr ((u v : g.vertex) ×' Path g u v) where
  reprPrec p n := reprPrec p.2.2 n

class Cycle (g : Graph) (u : g.vertex) where
  cycle : ClosedWalk g u
  is_path : Walk.isPath cycle

end HoG
