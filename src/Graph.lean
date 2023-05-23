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

-- adjacent vertices induce an edge
def Graph.adjacentEdge {G : Graph} {u v : G.vertex} :
  G.adjacent u v → G.edge := by
  apply lt_by_cases u v
  · intros u_lt_v uv
    constructor
    case val => exact Edge.mk v ⟨u, u_lt_v⟩
    case property => simp_all [u_lt_v, lt_by_cases, adjacent, badjacent]
  · intro u_eq_v
    intro H
    simp [u_eq_v, lt_by_cases, adjacent, badjacent] at H
  · intros v_lt_u uv
    constructor
    case val => exact Edge.mk u ⟨v, v_lt_u⟩
    case property => simp_all [v_lt_u, not_lt_of_lt, lt_by_cases, adjacent, badjacent]

lemma Graph.adjacentEdge_lt_fst {G : Graph} {u v : G.vertex} (uv : G.adjacent u v):
  u < v -> G.fst (G.adjacentEdge uv).val = v := by
  intro u_lt_v
  simp [u_lt_v, lt_by_cases, adjacentEdge]

lemma Graph.adjacentEdge_gt_fst {G : Graph} {u v : G.vertex} (uv : G.adjacent u v):
  v < u -> G.fst (G.adjacentEdge uv).val = u := by
  intro v_lt_u
  simp [v_lt_u, not_lt_of_lt, lt_by_cases, adjacentEdge]

lemma Graph.adjacentEdge_lt_snd {G : Graph} {u v : G.vertex} (uv : G.adjacent u v):
  u < v -> G.snd (G.adjacentEdge uv).val = u := by
  intro u_lt_v
  apply Fin.eq_of_val_eq
  simp [Fin.eq_of_val_eq, adjacentEdge, lt_by_cases, u_lt_v, not_lt_of_lt]
  sorry

lemma Graph.adjacentEdge_gt_snd {G : Graph} {u v : G.vertex} (uv : G.adjacent u v):
  v < u -> G.snd (G.adjacentEdge uv).val = v := by
  sorry

lemma Graph.irreflexiveNeighbor (G : Graph) :
  ∀ (v : G.vertex), ¬ adjacent v v := by simp [lt_by_cases, adjacent, badjacent]

lemma Graph.symmetricNeighbor (G : Graph) :
  ∀ (u v : G.vertex), adjacent u v → adjacent v u := by
    intros u v
    apply lt_by_cases u v <;> (intro h ; simp [lt_by_cases, not_lt_of_lt, h, adjacent, badjacent])

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
