import Graph
import ConnectedComponents
import TreeSet


-- -- [ ] Be able to define the functions on paths my pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Walk (g : SimpleIrreflexiveGraph) : Nat → Nat → Type
  | trivial (s : Nat) : Walk g s s
  | left (s t u : Nat) : (edgeRelation g) s t → Walk g t u →  Walk g s u
  | right (s t u : Nat) : (edgeRelation g) t u → Walk g s t → Walk g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro walk:term " ~- " "{" u:term "," v:term "}" : term => `(Walk.right _ $u $v (by rfl) $walk)
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Walk.left $u $v _ (by rfl) $walk)
macro " ⬝ " u:term : term => `(Walk.trivial $u)

def Walk.toString {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → String
  | .trivial s => s!"{s}"
  | .left s _ t er w => s!"{s} -> {w.toString}"
  | .right s _ t er w => s!"{w.toString} -> {t}"

instance walkToString {g : SimpleIrreflexiveGraph} {s t : Nat} : ToString (Walk g s t) where
  toString := fun w => w.toString

def Walk.isNontrivial {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → Prop
  | .trivial s => False
  | .left _ _ _ _ _ => True
  | .right _ _ _ _ _ => True

def Walk.notInWalk {g : SimpleIrreflexiveGraph} (u v a b : Nat) : Walk g u v → edgeRelation g a b → Bool
  | .trivial s, e => true
  | .left u t v _ p, e => (a != u || b != t) && (a != t || b != u) && notInWalk t v a b p e
  | .right u t v _ p, e => (a != t || b != v) && (a != v  || b != t) && notInWalk u t a b p e

def Walk.reverse {g : SimpleIrreflexiveGraph} {s t : Nat} :  Walk g s t → Walk g t s
  | .trivial s => .trivial s
  | .left s t u e p => Walk.right u t s (edgeRelationSymmetric e) (reverse p)
  | .right s t u e p => Walk.left u t s (edgeRelationSymmetric e) (reverse p)

macro p:term "↑" : term => `(Walk.reverse $p)

def Walk.concat {g : SimpleIrreflexiveGraph} {s t u : Nat} : Walk g s t → Walk g t u → Walk g s u := fun p q =>
  match p with
  | .trivial s => q
  | .left s v t e p' =>
    match q with
    | .trivial t => Walk.left s v t e p'
    | .left t w u r q' => Walk.left s v u e (concat (Walk.right v t w r p') q')
    | .right t w u r q' => Walk.left s v u e (Walk.right v w u r (concat p' q'))
  | p' =>
    match q with
    | .trivial t => p'
    | .left t w u r q' => concat (Walk.right s t w r p') q'
    | .right t w u r q' => Walk.right s w u r (concat p' q')

macro p:term "+" q:term : term => `(Walk.concat $p $q)

def Walk.edgeWalk {g : SimpleIrreflexiveGraph} {s t : Nat} : (edgeRelation g) s t → Walk g s t := fun e =>
  Walk.left s t t e (Walk.trivial t)

def Walk.length {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → ℕ
  | .trivial s => 0
  | .left s _ t e p' => length p' + 1
  | .right s _ t e p' => length p' + 1

-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : SimpleIrreflexiveGraph} {s t : Nat} : Walk g s t → connected g s t
  | .trivial s => connectedRefl
  | .left s _ t e p' => (edgeConnected e) ⊕ (pathImpliesConnected p')
  | .right s _ t e p' => pathImpliesConnected p' ⊕ (edgeConnected e)

theorem moo (α : Type) (f : α → ℕ) (P : α → Type)
  (base : ∀ a, f a = 0 → P a)
  (ind : ∀ a, (∀ b, f b < f a → P b) → P a) :
  ∀ a, P a := by
  intro a
  let Q := fun n => ∀ a, f a = n → P a
  have Qstep : ∀ (n : ℕ), (∀ (m : ℕ), m < n → Q m) → Q n
  { intros n h a ξ
    apply (ind a)
    intros b fb_lt_fa
    rw [ξ] at fb_lt_fa
    apply (h (f b)) fb_lt_fa
    rfl
  }
  exact @WellFounded.fix _ Q Nat.lt Nat.lt_wfRel.wf Qstep (f a) a rfl

lemma witnessWalkToRoot (w : numComponentsWitnessExact) (s : Fin w.G.vertexSize) : Walk w.G s (w.root (w.c s)) := by
  apply @moo (Fin w.G.vertexSize) (w.h) (fun v => Walk w.G v (w.root (w.c v)))
  { intros v H
    have h := w.uniquenessOfRoots v H
    rw [←h]
    apply Walk.trivial
  }
  { intros v h
    by_cases H : (0 < w.h v)
    · let u := w.next v
      let hyp := w.heightCond v H
      have p : Walk w.G u (w.root (w.c u)) := by apply h; cases hyp; assumption
      have same_c : w.c ↑u = w.c ↑v := by
        have er : edgeRelation w.G ↑u ↑v := by simp [hyp]
        apply @Nat.lt_by_cases u v
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
  }


inductive Path (g : SimpleIrreflexiveGraph) : Nat → Nat → Type
  | left (s t u : Nat) (er : edgeRelation g s t) (w : Walk g t u) : Walk.notInWalk t u s t w er →  Path g s u
  | right (s t u : Nat) (er : edgeRelation g t u) (w : Walk g s t) : Walk.notInWalk s t t u w er → Path g s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro walk:term " ~- " "{" u:term "," v:term "}" : term => `(Path.right _ $u $v (by rfl) $walk (by bool_reflect))
macro "{" u:term "," v:term "}" " -~ " walk:term : term => `(Path.left $u $v _ (by rfl) $walk (by bool_reflect))
macro " ⬝ " u:term : term => `(Path.trivial $u)

def Path.toString {g : SimpleIrreflexiveGraph} {s t : Nat} : Path g s t → String
  | .left _ _ _ _ w _ => s!"{s} -> {w.toString}"
  | .right _ _ _ _ w _ => s!"{w.toString} -> {t}"

instance pathToString {g : SimpleIrreflexiveGraph} {s t : Nat} : ToString (Path g s t) where
  toString := fun w => w.toString

def Path.length {g : SimpleIrreflexiveGraph} {s t : Nat} : Path g s t → Nat
  | .left _ u _ er w h => w.length + 1
  | .right _ u _ er w h => w.length + 1

-- A cycle is a path from a vertex to itself
def Cycle (g : SimpleIrreflexiveGraph) (u : Nat) : Type := Path g u u

def Cycle.length {g : SimpleIrreflexiveGraph} {u : Nat} : Cycle g u → Nat := fun c => Path.length c