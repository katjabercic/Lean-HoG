import JSON2Lean.Graph

namespace JSON2Lean

/- Basic facts about connected and disconnected graphs. -/

/-- Vertices are connected iff they are relaeted by the equivalence envelope of adjacency -/
def Graph.connected {G : Graph} : G.vertex → G.vertex → Prop := EqvGen G.adjacent

/-- Adjacent vertices are connected -/
lemma Graph.connected_of_adjacent {G : Graph} {u v : G.vertex} :
    G.adjacent u v → G.connected u v :=
  EqvGen.rel u v

/-- Equal vertices are connected -/
lemma Graph.connected_of_eq {G : Graph} (u v : G.vertex) : u = v → G.connected u v := by
  intro eq
  rw [eq]
  apply EqvGen.refl

/-- Connectedness is transitive -/
lemma Graph.connected_trans {G : Graph} (u v w : G.vertex) :
  G.connected u v → G.connected v w → G.connected u w :=
  EqvGen.trans u v w

/-- We may extend connectedness by an edge -/
lemma Graph.adjacentConnected {G : Graph} (u v w : G.vertex) :
  G.adjacent u v → G.connected v w → G.connected u w := by
  intros uv vw
  apply connected_trans (v := v)
  · apply EqvGen.rel ; assumption
  · exact vw

/-- Connectedness is symmetric -/
lemma Graph.connected_symm {G : Graph} (u v : G.vertex) :
  G.connected u v → G.connected v u :=
  EqvGen.symm u v

/-- Auxuliary induction principle (think of f x as a "height" of x) -/
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

/-- A certificate witnessing that a graph is connected -/
class ConnectivityCertificate (G : Graph) where
  /-- A vertex that every other vertex is connected to -/
  root : G.vertex

  /-- A map taking each vertex closer to the root -/
  next : G.vertex → G.vertex

  /--
    Map each vertex to the distance to its root.
    (It does not actually have to be the distance, it suffices
    that it satisfy the conditions given below.) -/
  distToRoot : G.vertex → Nat

  /-- Each vertex that is not a root is adjacent to the next one -/
  nextAdjacent : ∀ v, v ≠ root → G.adjacent v (next v)

  /-- distance to root decreases as we travel along the path given by next -/
  distNext : ∀ v, v ≠ root → distToRoot (next v) < distToRoot v


/-- Given a connected certificate, each vertex is connected to the root -/
lemma connectedToRoot (G : Graph) [C : ConnectivityCertificate G] :
  ∀ v, G.connected v C.root := by
  apply heightInduction C.distToRoot (fun v => G.connected v C.root)
  intros v ih
  cases (Decidable.eq_or_ne v C.root)
  case inl eq => apply G.connected_of_eq ; assumption
  case inr neq =>
    apply G.adjacentConnected v (C.next v) C.root
    · apply C.nextAdjacent ; assumption
    · apply ih
      apply C.distNext
      assumption

/-- A graph is connected it is has a connectivity certificate.  -/
theorem Graph.is_connected (G : Graph) [C : ConnectivityCertificate G] : ∀ u v, G.connected u v := by
  intros u v
  apply G.connected_trans
  · apply connectedToRoot
  · apply G.connected_symm
    apply connectedToRoot

/-- A certificate witnessing that a graph is disconnected. -/
class DisconnectivityCertificate (G : Graph) where

  /-- A coloring of vertices by two colors -/
  color : G.vertex → Fin 2

  /-- A vertex of color 0 -/
  vertex0 : G.vertex

  /-- A vertex of color 1-/
  vertex1 : G.vertex

  /-- Neighbors have the same color -/
  edgeColor : ∀ (e : G.edge), color e.val.fst = color e.val.snd

  /-- Vertex 0 has color 0 -/
  vertex0Color : color vertex0 = 0

  /-- Vertex 1 has color 1 -/
  vertex1Color : color vertex1 = 1

/-- Connected vertices have the same color -/
lemma connected_color {G : Graph} [D : DisconnectivityCertificate G] (u v : G.vertex) :
    G.connected u v → D.color u = D.color v  := by
  intro Cuv
  induction Cuv
  case rel a b adj =>
     apply G.all_adjacent_of_edges (fun a b => D.color a = D.color b)
     · intros u v eq
       symm
       assumption
     · exact D.edgeColor
     · assumption
  case refl a => rfl
  case symm a b _ eq => apply Eq.symm eq
  case trans a b c _ _ eq1 eq2 => apply Eq.trans eq1 eq2

/-- Given a certificate of disconnectivity, the graph is disconnected -/
theorem Graph.is_disconnected (G : Graph) [D : DisconnectivityCertificate G] : ∃ u v, ¬ G.connected u v := by
  exists D.vertex0, D.vertex1
  intro C01
  apply @absurd (D.color D.vertex0 = D.color D.vertex1)
  · apply connected_color
    assumption
  · simp [D.vertex0Color, D.vertex1Color]

end JSON2Lean
