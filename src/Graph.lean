import OrdEq
import TreeSet
import TreeMap
import Edge

namespace HoG

structure Graph : Type :=
  vertexSize : Nat
  edgeTree : STree (Edge vertexSize)
  -- edgeCorrect : edgeTree.correct := by rfl

-- the type of graph vertices
@[simp, reducible]
def Graph.vertex (G : Graph) := Fin G.vertexSize

-- the underlying type of edges (pairs (i,j) such that j < i < G.vertexSize)
@[simp, reducible]
def Graph.edgeType (G : Graph) := Edge G.vertexSize

-- the type of edges
@[simp, reducible]
def Graph.edge (G : Graph) := { e : G.edgeType // G.edgeTree.mem e }

@[simp]
def Graph.fst {G : Graph} (e : G.edgeType) : G.vertex := e.fst

@[simp]
def Graph.snd {G : Graph} (e : G.edgeType) : G.vertex :=
  ⟨e.snd, lt_trans e.snd.isLt e.fst.isLt⟩

-- the number of eges in a graph
def Graph.edgeSize (G : Graph) := Fintype.card G.edge

-- the vertex adjacency relation
def Graph.badjacent {G : Graph} : G.vertex → G.vertex → Bool :=
  fun u v =>
    lt_by_cases u v
      (fun u_lt_v => G.edgeTree.mem (Edge.mk v (Fin.mk u u_lt_v)))
      (fun _ => false)
      (fun v_lt_u => G.edgeTree.mem (Edge.mk u (Fin.mk v v_lt_u)))

def Graph.adjacent {G : Graph} : G.vertex → G.vertex → Prop :=
  fun u v => G.badjacent u v

instance (G : Graph) : DecidableRel G.adjacent := by
  intros u v
  unfold Graph.adjacent
  infer_instance

-- There is an edge between adjacent vertices
def Graph.adjacentEdge {G : Graph} {u v : G.vertex} :
  G.adjacent u v → { e : G.edge // (G.fst e = u ∧ G.snd e = v) ∨ (G.fst e = v ∧ G.snd e = u) } := by
  apply lt_by_cases u v <;> intro H <;> simp [H, not_lt_of_lt, adjacent, badjacent, lt_by_cases]
  · intro e_mem
    let e : G.edge := ⟨ Edge.mk_lt H, (by simp [e_mem, Edge.mk_lt]) ⟩ 
    exists e
    simp [Edge.mk_lt]
  · intro ; contradiction
  · intro e_mem
    let e : G.edge := ⟨ Edge.mk_lt H, (by simp [e_mem, Edge.mk_lt]) ⟩ 
    exists e
    simp [Edge.mk_lt]

lemma Graph.irreflexiveNeighbor (G : Graph) :
  ∀ (v : G.vertex), ¬ adjacent v v := by simp [lt_by_cases, adjacent, badjacent]

lemma Graph.symmetricNeighbor (G : Graph) :
  ∀ (u v : G.vertex), adjacent u v → adjacent v u := by
    intros u v
    apply lt_by_cases u v <;> (intro h ; simp [lt_by_cases, not_lt_of_lt, h, adjacent, badjacent])

-- checking that a symetric relations holds for all pairs of adjacent vertices
-- reduces to checking it for all edges
lemma Graph.adjacentAll (G : Graph)
  (p : G.vertex → G.vertex → Prop) [DecidableRel p] :
  G.edgeTree.all (fun e => p (G.fst e) (G.snd e)) → ∀ u v, G.adjacent u v → p u v ∨ p v u := by 
  intros eA u v uv
  cases G.adjacentEdge uv with
  | mk e r =>
    have pe := G.edgeTree.all_forall (fun e => p (G.fst e) (G.snd e)) eA e e.property
    cases r with
    | inl eq => apply Or.inl ; rw [←eq.1, ←eq.2] ; exact pe
    | inr eq => apply Or.inr ; rw [←eq.1, ←eq.2] ; exact pe

lemma Graph.adajcentAllSymm (G : Graph)
  (p : G.vertex → G.vertex → Prop) [DecidableRel p]:
  Symmetric p → G.edgeTree.all (fun e => p (G.fst e) (G.snd e)) → ∀ u v, G.adjacent u v → p u v := by
  intros sp eA u v uv
  cases G.adjacentAll p eA u v uv
  · assumption
  · apply sp ; assumption

-- the neighborhood of a graph
@[reducible]
def Graph.neighborhood (G : Graph) (v : G.vertex) :=
  { u : G.vertex // G.badjacent v u }

-- the degree of a vertex
def Graph.degree (G : Graph) (v : G.vertex) : Nat := Fintype.card (G.neighborhood v)

-- the minimal vertex degree
def Graph.minDegree (G : Graph) : WithTop Nat :=
  Finset.inf (Fin.fintype G.vertexSize).elems (fun v => G.degree v)

-- the maximal vertex degree
def Graph.maxDegree (G : Graph) : WithBot Nat :=
  Finset.sup (Fin.fintype G.vertexSize).elems (fun v => G.degree v)

end HoG
