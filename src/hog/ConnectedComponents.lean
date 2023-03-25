-- -- Graph components
import Mathlib.Init.Data.Quot
import Mathlib.Logic.Basic
import Mathlib.Init.Function
import Init.WF
import Graph
import TreeSet

@[simp, reducible]
def connected (G : SimpleIrreflexiveGraph) : Nat → Nat → Prop := EqvGen (edgeRelation G)

macro g:term "|-" v:term "≈" u:term : term => `(connected $g $v $u)

@[simp]
lemma edgeConnected {G : SimpleIrreflexiveGraph} {u v : Nat} (e : (edgeRelation G) u v) : 
  connected G u v := EqvGen.rel u v e

@[simp]
lemma connectedRefl {G : SimpleIrreflexiveGraph} {v : Nat} : connected G v v := EqvGen.refl v

@[simp]
lemma connectedTrans {G : SimpleIrreflexiveGraph} {u v w : Nat} (cuv : connected G u v) (cvw : connected G v w) : 
  connected G u w := EqvGen.trans u v w cuv cvw

notation p "⊕" q => connectedTrans p q

@[simp]
lemma connectedSymm {G : SimpleIrreflexiveGraph} {u v : Nat} (cuv : connected G u v) : 
  connected G v u := EqvGen.symm u v cuv

notation p "↑" => connectedSymm p

-- -- because connectedness if defined as an equivalence relation, two connected vertices cannot be equal
@[simp]
lemma notConnectedNotEqual {G : SimpleIrreflexiveGraph} {u v : Nat} : ¬connected G u v → ¬u = v := by
  intro h
  by_contra
  suffices h' : connected G u v
  contradiction
  have eq : u = v := by trivial
  rw [eq]
  apply connectedRefl

def connectedGraph : SimpleIrreflexiveGraph → Prop := fun G => ∀ (u v : Nat), connected G u v

structure numberOfConnectedComponents : Type :=
  (G : SimpleIrreflexiveGraph)
  (numComponents : Nat)
  (c : Nat → Fin numComponents)
  (hasEnough : ∀ (i : Fin numComponents), ∃ u, c u = i)
  (conn : ∀ u v, c u = c v ↔ connected G u v)

structure numComponentsWitnessLoose : Type :=
  (G : SimpleIrreflexiveGraph)
  (numComponents : Nat)
  (c : Nat → Fin numComponents)
  (h : Nat → Nat)
  (connectEdges : ∀ (e : Edge), (e ∈ G.edges) → c e.edge.fst = c e.edge.snd)
  (root : Fin numComponents → Fin G.vertexSize)
  (isRoot :  ∀ i, c (root i) = i ∧ h (root i) = 0)
  (uniquenessOfRoots : ∀ v, h v = 0 → v = root (c v))
  (next : Nat → Nat) -- for each vertex with height > 0, give a neighbor with lower height
  (heightCond : ∀ v, (0 < h v) → (edgeRelation G) (next v) v ∧ h (next v) < h v)

structure numComponentsWitnessExact : Type :=
  (G : SimpleIrreflexiveGraph)
  (numComponents : Nat)
  (c : Nat → Fin numComponents)
  (h : Fin G.vertexSize → Nat)
  (connectEdges : ∀ (e : Edge), (e ∈ G.edges) → c e.edge.fst = c e.edge.snd)
  (root : Fin numComponents → Fin G.vertexSize)
  (isRoot :  ∀ i, c (root i) = i ∧ h (root i) = 0)
  (uniquenessOfRoots : ∀ v, h v = 0 → v = root (c v))
  (next : Nat → Fin G.vertexSize) -- for each vertex with height > 0, give a neighbor with lower height
  (heightCond : ∀ v, (0 < h v) → (edgeRelation G) (next v) v ∧ h (next v) < h v)

-- def transformWitness : numComponentsWitnessExact → numComponentsWitnessLoose := fun w =>
--   {
--     G := w.G
--     numComponents := w.numComponents
--     c := w.c
--     h := fun v => by
--       by_cases (v < w.G.vertexSize)
--       · apply w.h (Fin.mk v h)
--       · exact 0
--     connectEdges := w.connectEdges
--     root := w.root
--     isRoot := fun v => by simp; apply w.isRoot
--     uniquenessOfRoots := fun v => sorry
--     next := sorry
--     heightCond := sorry
--   }

theorem foo (α : Type) (f : α → Nat) (P : α → Prop)
  (base : ∀ a, f a = 0 → P a)
  (ind : ∀ a, (∀ b, f b < f a → P b) → P a) :
  ∀ a, P a := by
  intro a
  let Q := fun n => ∀ a, f a = n → P a
  have Qstep : ∀ (n : Nat), (∀ (m : Nat), m < n → Q m) → Q n
  { intros n h a ξ
    apply (ind a)
    intros b fb_lt_fa
    rw [ξ] at fb_lt_fa
    apply (h (f b)) fb_lt_fa
    rfl
  }
  exact @WellFounded.fix _ Q Nat.lt (Nat.lt_wfRel.wf) Qstep (f a) a rfl

-- Different proof of foo using strong induction
-- theorem bar (α : Type) (f : α → Nat) (P : α → Prop)
--   (ind : ∀ a, (∀ b, f b < f a → P b) → P a) :
--   ∀ a, P a :=
-- begin
--   intro a,
--   induction hn : f a using nat.strong_induction_on with n ih generalizing a,
--   apply ind,
--   intros b fb_lt_fa,
--   rw hn at fb_lt_fa,
--   exact ih _ fb_lt_fa _ rfl,
-- end

lemma connectedToRoot (w : numComponentsWitnessLoose) : 
  ∀ v : Nat, connected w.G v (w.root (w.c v)) := by
  fapply @foo Nat (w.h) (fun u => connected w.G u (w.root (w.c u)))
  { intros v h
    have h := w.uniquenessOfRoots v h
    rw [←h]
    apply connectedRefl
  }
  { intros v h
    by_cases H : (0 < w.h v)
    { let u := w.next v
      have hyp := w.heightCond v H
      have H' : connected w.G u (w.root (w.c u)) := by apply h; cases hyp; assumption
      have same_c : w.c u = w.c v := 
        by
          apply lt_by_cases u v
          { intros uv -- u < v
            let e : Edge := { edge := (u, v), src_lt_trg := uv }
            have euv : e ∈ w.G.edges
            cases hyp
            apply edgeRelationIsMem (by assumption)
            apply w.connectEdges e euv
          }
          { intros uv -- u = v
            rw [uv]
          }
          { intros vu -- v < u
            let e : Edge := { edge := (v, u), src_lt_trg := vu }
            have evu : e ∈ w.G.edges
            cases hyp
            apply edgeRelationIsMem (edgeRelationSymmetric (by assumption))
            apply symm
            apply w.connectEdges e evu
          }
      rw [←same_c]
      have cuv : connected w.G u v := by
        apply edgeConnected; cases hyp; assumption
      exact cuv↑ ⊕ H'
    }
    { simp at H
      have h := w.uniquenessOfRoots v H
      rw [←h]
      apply connectedRefl
    }
  }

lemma connectedToRootExact (w : numComponentsWitnessExact) : 
  ∀ v : (Fin w.G.vertexSize), connected w.G v (w.root (w.c v)) := by
  fapply @foo (Fin w.G.vertexSize) (w.h) (fun u => connected w.G u (w.root (w.c u)))
  { intros v h
    have h := w.uniquenessOfRoots v h
    rw [←h]
    apply connectedRefl
  }
  { intros v h
    by_cases H : (0 < w.h v)
    { let u := w.next v
      have hyp := w.heightCond v H
      have H' : connected w.G u (w.root (w.c u)) := by apply h; cases hyp; assumption
      have same_c : w.c u = w.c v := 
        by
          apply lt_by_cases u v
          { intros uv -- u < v
            let e : Edge := { edge := (u, v), src_lt_trg := uv }
            have euv : e ∈ w.G.edges
            cases hyp
            apply edgeRelationIsMem (by assumption)
            apply w.connectEdges e euv
          }
          { intros uv -- u = v
            rw [uv]
          }
          { intros vu -- v < u
            let e : Edge := { edge := (v, u), src_lt_trg := vu }
            have evu : e ∈ w.G.edges
            cases hyp
            apply edgeRelationIsMem (edgeRelationSymmetric (by assumption))
            apply symm
            apply w.connectEdges e evu
          }
      rw [←same_c]
      have cuv : connected w.G u v := by
        apply edgeConnected; cases hyp; assumption
      exact cuv↑ ⊕ H'
    }
    { simp at H
      have h := w.uniquenessOfRoots v H
      rw [←h]
      apply connectedRefl
    }
  }

lemma witnessConnectedCondition (w : numComponentsWitnessLoose) : ∀ u v, w.c u = w.c v ↔ connected w.G u v := by
  intros u v
  apply Iff.intro
  · intro H
    have connectedToRoot : ∀ x : Nat, connected w.G x (w.root (w.c x))
    { intro x
      apply connectedToRoot
    }
    { have h : connected w.G u (w.root (w.c u)) := connectedToRoot u
      have h' : connected w.G v (w.root (w.c v)) := connectedToRoot v
      have h'' : w.root (w.c u) = w.root (w.c v) := by rw [H]
      rw [h''] at h
      exact h ⊕ (h' ↑)
    }
  · intro h
    induction h with
    | rel u v rel_uv =>
      {
        apply lt_by_cases u v
        · intro uv
          let e : Edge := { edge := (u, v), src_lt_trg := uv }
          have euv : e ∈ w.G.edges
          apply edgeRelationIsMem rel_uv
          apply w.connectEdges e euv
        · intro uv
          rw [uv]
        · intro vu
          let e : Edge := { edge := (v, u), src_lt_trg := vu }
          have evu : e ∈ w.G.edges
          apply edgeRelationIsMem (edgeRelationSymmetric rel_uv)
          apply symm
          apply w.connectEdges e evu
      }
    | refl u => rfl
    | symm u v =>
      apply symm
      assumption
    | trans u v w =>
      trans
      assumption
      assumption

theorem witnessComponents : numComponentsWitnessLoose → numberOfConnectedComponents :=
  fun w =>
    {
      G := w.G,
      numComponents := w.numComponents,
      c := w.c,
      hasEnough := by
        have h : Function.HasRightInverse w.c
        unfold Function.HasRightInverse
        apply Exists.intro
        unfold Function.RightInverse
        unfold Function.LeftInverse
        intro x
        have isRoot := w.isRoot x
        apply isRoot.left
        apply Iff.mpr Function.surjective_iff_hasRightInverse
        assumption
      conn := by apply witnessConnectedCondition,
    }
