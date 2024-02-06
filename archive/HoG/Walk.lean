import HoG.Graph
import HoG.Invariant.ConnectedComponents
import HoG.TreeSet


-- -- [ ] Be able to define the functions on paths my pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Walk (g : SimpleIrreflexiveGraph) : Nat → Nat → Type
  | trivial (s : Nat) : g.isVertex s → Walk g s s
  | left {s t u : Nat} : g[s ~~ t] → Walk g t u →  Walk g s u
  | right {s t u : Nat} : Walk g s t → g[t ~~ u] → Walk g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro walk:term " ~- " "{" u:term "," v:term "}" : term => `(Walk.right _ $u $v (by rfl) $walk)
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Walk.left $u $v _ $walk (by rfl))
macro " ⬝ " u:term : term => `(Walk.trivial $u)

def Walk.toString {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → String
  | .trivial s _ => s!"{s}"
  | .left e w => s!"{s} -> {w.toString}"
  | .right w e => s!"{w.toString} -> {t}"

instance walkToString {g : SimpleIrreflexiveGraph} {s t : Nat} : ToString (Walk g s t) where
  toString := fun w => w.toString

def Walk.isNontrivial {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → Prop
  | .trivial s _ => False
  | .left _ _ => True
  | .right _ _ => True

def Walk.notInWalk {g : SimpleIrreflexiveGraph} {u v a b : Nat} : Walk g u v → edgeRelation g a b → Bool
  | .trivial s _, e => true
  | .left (t := t) _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk p e
  | .right (t := t) p _, e => (a != t || b != v) && (a != v  || b != t) && notInWalk p e

def Walk.reverse {g : SimpleIrreflexiveGraph} {s t : Nat} :  Walk g s t → Walk g t s
  | .trivial s p => .trivial s p
  | .left e p => Walk.right (reverse p) (edgeRelationSymmetric e)
  | .right p e => Walk.left (edgeRelationSymmetric e) (reverse p)

macro p:term "↑" : term => `(Walk.reverse $p)

def Walk.concat {g : SimpleIrreflexiveGraph} {s t u : Nat} : Walk g s t → Walk g t u → Walk g s u := fun p q =>
  match p with
  | .trivial s _ => q
  | .left e p' =>
    match q with
    | .trivial t _ => Walk.left e p'
    | .left r q' => Walk.left e (concat (Walk.right p' r) q')
    | .right q' r => Walk.left e (Walk.right (concat p' q') r)
  | p' =>
    match q with
    | .trivial t _ => p'
    | .left r q' => concat (Walk.right p' r) q'
    | .right q' r => Walk.right (concat p' q') r

macro p:term "+" q:term : term => `(Walk.concat $p $q)

def Walk.edgeWalk {g : SimpleIrreflexiveGraph} {s t : Nat} (e : g[s ~~ t]) : Walk g s t :=
  Walk.left e (Walk.trivial t (endpointIsVertex g e).right)

def Walk.length {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → ℕ
  | .trivial s _ => 0
  | .left _ p' => length p' + 1
  | .right p' _ => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → connected g s t
  | .trivial s _ => connectedRefl
  | .left e p' => (edgeConnected e) ⊕ (pathImpliesConnected p')
  | .right p' e => pathImpliesConnected p' ⊕ (edgeConnected e)

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

lemma witnessWalkToRoot (w : numComponentsWitnessExact) (s : Fin w.G.vertexSize) : Walk w.G s (w.root (w.c s)) := by
  apply @strongInduction (Fin w.G.vertexSize) (w.h) (fun v => Walk w.G v (w.root (w.c v)))
  { intros v h
    by_cases H : (0 < w.h v)
    · let u := w.next v
      let hyp := w.heightCond v H
      have p : Walk w.G u (w.root (w.c u)) := by apply h; cases hyp; assumption
      have same_c : w.c ↑u = w.c ↑v := by
        have er : edgeRelation w.G ↑u ↑v := by simp [hyp]
        apply ltByCases u v
        · intro H'
          let e : Edge := Edge.mk (u, v)
          apply w.connectEdges e (edgeRelationIsMem er)
        · intro H'
          rw [H']
        · intro H'
          let e : Edge := Edge.mk (v, u)
          have er' : edgeRelation w.G ↑v ↑u := by apply edgeRelationSymmetric er
          apply Eq.symm
          apply w.connectEdges e (edgeRelationIsMem er')
      rw [←same_c]
      have q : Walk w.G u v := by apply Walk.edgeWalk; cases hyp; assumption
      exact (q ↑) + p
    · simp at H
      have h := w.uniquenessOfRoots v H
      rw [←h]
      apply Walk.trivial
      sorry -- apply v.isLt
  }

def ClosedWalk (g : SimpleIrreflexiveGraph) : Type := Σ u : ℕ, Walk g u u

def ClosedWalk.length {g : SimpleIrreflexiveGraph} (w : ClosedWalk g) : Nat := Walk.length w.snd
