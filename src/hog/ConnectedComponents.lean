-- -- Graph components
import Mathlib.Init.Data.Quot
import Mathlib.Logic.Basic
import Mathlib.Init.Function
import Init.WF
import Graph
import TreeSet
import TreeMap

namespace HoG

@[simp]
def Graph.connected {G : Graph} : G.vertex → G.vertex → Prop := EqvGen G.adjacent

-- Neighbors are connected
lemma Graph.adjacentConected {G : Graph} {u v : G.vertex} : G.adjacent u v → G.connected u v :=
  EqvGen.rel u v

-- Equal vertices are connected
lemma Graph.connectedEq {G : Graph} (u v : G.vertex) : u = v → G.connected u v := by
  intro eq
  rw [eq]
  apply EqvGen.refl

-- Connectedness is transitive
@[simp]
lemma Graph.connectedTrans {G : Graph} (u v w : G.vertex) :
  G.connected u v → G.connected v w → G.connected u w :=
  EqvGen.trans u v w

lemma Graph.adjacentConnected {G : Graph} (u v w : G.vertex) :
  G.adjacent u v → G.connected v w → G.connected u w := by
  intros uv vw
  apply connectedTrans (v := v)
  · apply EqvGen.rel ; assumption
  · exact vw

@[simp]
lemma Graph.connectedSymm {G : Graph} (u v : G.vertex) :
  G.connected u v → G.connected v u :=
  EqvGen.symm u v

def Graph.is_connected (G : Graph) := ∀ (u v : G.vertex), G.connected u v

-- Connected components of a graph
class ConnectedComponents (G : Graph) : Type :=
  val : Nat -- number of components
  component : G.vertex → Fin val -- assigns a component to each vertex
  componentInhabited : ∀ (i : Fin val), ∃ u, component u = i -- each component is inhabited
  correct : ∀ u v, component u = component v ↔ G.connected u v

-- Is this silly lemma somewhere in the prelude?
lemma zero_or_lt : ∀ (n : Nat), n = 0 ∨ 0 < n := by
  intro n
  cases n
  · apply Or.inl ; simp
  · apply Or.inr ; simp

-- A certificate for connected components:
class ComponentsCertificate (G : Graph) : Type :=
  -- number of components
  val : Nat
  -- assignment of components to each vertex
  component : G.vertex → Fin val
  -- the endpoints of an edge are in the same component
  componentEdge : G.edgeTree.all (fun e => component (G.fst e) = component (G.snd e)) = true
  -- for each component, a chosen representative, called "the component root"
  root : Fin val → G.vertex
  -- each root is in the correct component
  rootCorrect : (∀ i, component (root i) = i) = true

  -- For each component we give a directed spanning tree rooted at its component root.
  -- We call this tree the "component tree". All the component trees form a spanning forest.

  -- for each vertex that is not a root, the next step of the path leading to its root
  -- (and roots map to themselves)
  next : G.vertex → G.vertex
  -- To ensure that next is cycle-free, we witness the fact that it takes us closer to the root.
  -- the distance of a vertex to its component root
  distToRoot : G.vertex → Nat
  -- a root is at distance 0 from itself
  distRootZero : (∀ i, distToRoot (root i) = 0) = true
  -- a vertex is a root if its distance to a root is 0
  distZeroRoot : (∀ v, distToRoot v = 0 → v = root (component v)) = true
  -- a root is a fixed point of next
  nextRoot : (∀ i, next (root i) = root i) = true
  -- each vertex that is not a root is adjacent to the next one
  nextAdjacent : (forall v, 0 < distToRoot v → G.adjacent v (next v)) = true
  -- distance to root decreases as we travel along the path given by next
  distNext : (∀ v, 0 < distToRoot v → distToRoot (next v) < distToRoot v) = true

def ComponentsCertificate.componentEdge' {G : Graph} [C : ComponentsCertificate G] :
  ∀ (e : G.edge), component (G.fst e.val) = component (G.snd e.val) := by
  intro e
  apply G.edgeTree.all_forall (fun e => component (G.fst e) = component (G.snd e)) C.componentEdge
  exact e.property

-- adjacent vertices are in the same component
lemma ComponentsCertificate.componentAdjacent {G} [C : ComponentsCertificate G] :
  ∀ u v, G.adjacent u v → component u = component v := by
  intros u v uv
  let ce := C.componentEdge' (G.adjacentEdge uv).val
  apply lt_by_cases u v
  · intro u_lt_v
    rw [Graph.adjacentEdge_lt_fst uv u_lt_v, Graph.adjacentEdge_lt_snd uv u_lt_v] at ce
    symm
    assumption
  · intro eq
    apply congrArg
    assumption
  · intro v_lt_u
    rw [Graph.adjacentEdge_gt_fst uv v_lt_u, Graph.adjacentEdge_gt_snd uv v_lt_u] at ce
    assumption

-- the root of the component of a given vertex
@[simp]
def ComponentsCertificate.rootOf {G} [C : ComponentsCertificate G] : G.vertex → G.vertex :=
  (fun (v : G.vertex) => C.root (C.component v))

def ComponentsCertificate.rootOfNext {G} [C : ComponentsCertificate G] (v : G.vertex) :
  C.rootOf (C.next v) = C.rootOf v := by
  apply congrArg C.root
  cases zero_or_lt (C.distToRoot v)
  case inl eq =>
    apply congrArg
    apply Eq.symm
    rw [C.distZeroRoot v eq]
    apply Eq.symm
    apply C.nextRoot
  case inr _ =>
    apply Eq.symm
    apply C.componentAdjacent
    apply C.nextAdjacent
    assumption

-- Auxuliary induction principle (think of f x as a "height" of x)
theorem heightInduction {α : Type} (f : α → Nat) (P : α → Prop) :
  (∀ x, (∀ y, f y < f x → P y) → P x) → ∀ x, P x := by
  intros ind a
  let Q := fun n => ∀ a, f a = n → P a
  have Qstep : ∀ n, (∀ m, m < n → Q m) → Q n
  { intros n h a ξ
    apply (ind a)
    intros b fb_lt_fa
    rw [ξ] at fb_lt_fa
    apply (h (f b)) fb_lt_fa
    rfl
  }
  exact @WellFounded.fix _ Q Nat.lt (Nat.lt_wfRel.wf) Qstep (f a) a rfl

-- Given a component certificate, each vertex is connected to its root
lemma connectedToRoot (G : Graph) [C : ComponentsCertificate G] :
  ∀ v, G.connected v (C.rootOf v) := by
  apply heightInduction C.distToRoot (fun v => G.connected v (C.rootOf v))
  intros v ih
  cases (zero_or_lt (C.distToRoot v))
  · apply G.connectedEq
    apply C.distZeroRoot v
    assumption
  · apply G.adjacentConnected v (C.next v) (C.rootOf v)
    · apply C.nextAdjacent ; assumption
    · rw [Eq.symm (C.rootOfNext v)]
      apply ih
      apply C.distNext
      assumption

-- From a components certificate we can derive the connected components
instance {G : Graph} [C : ComponentsCertificate G] : ConnectedComponents G :=
  { val := C.val ,
    component := C.component,
    componentInhabited := by { intro i ; exists (C.root i) ; apply C.rootCorrect },
    correct := by
      intros u v
      apply Iff.intro
      · intro eq
        apply G.connectedTrans u (C.rootOf u) v
        · apply connectedToRoot
        · apply Graph.connectedSymm
          unfold ComponentsCertificate.rootOf
          rw [eq]
          apply connectedToRoot
      · intro uv
        induction uv
        case mpr.rel x y xy => apply C.componentAdjacent ; assumption
        case mpr.refl => rfl
        case mpr.symm => apply Eq.symm ; assumption
        case mpr.trans eq₁ eq₂ => apply Eq.trans eq₁ eq₂
  }

end HoG
