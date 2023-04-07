import Lean
import Mathlib.Order.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Prod.Lex
import Mathlib.Init.Algebra.Order
import Init.Prelude
import TreeSet
import TreeMap
import Tactic

open TreeSet
open TreeMap

-- The type of edges
structure Edge : Type :=
  edge        : Lex (Nat × Nat)
  src_lt_trg  : edge.fst < edge.snd := by trivial

instance EdgeLinearOrder : LinearOrder Edge := 
  LinearOrder.lift' (fun (u : Edge) => u.edge) (fun u v H => by cases u; cases v; simp; assumption)

-- def nbhds_condition (nbhds : tmap ℕ (tset ℕ)) : Prop :=
--   ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → i ∈ nbhds.to_map j)

-- theorem test (nbhds : Tmap ℕ (Tset ℕ)) : DecidablePred (fun j => i ∈ nbhds.toMap j) := by
--   intro j

instance (nbhds : Tmap ℕ (Tset ℕ)) : DecidablePred fun j => i ∈ Tmap.toMap nbhds j := by
  intro j
  let d : Decidable (i ∈ Tmap.toMap nbhds j) := by
    cases (Smap.valAt j nbhds)
    · simp [Tset.optionMem, Tset.optionHasMem]
      infer_instance
    · simp [Tset.optionMem, Tset.optionHasMem]
      infer_instance
  trivial

def decidableNbhdsCondition (nbhds : Tmap ℕ (Tset ℕ)) : Bool :=
  Smap.forallKeys (fun i => Stree.optionForall (fun j => i ∈ nbhds.toMap j) (nbhds.toMap i)) nbhds

-- def nbhds_describe_edges (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : Prop := 
--   ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → decidable.lt_by_cases i j
--     (λ _, {edge . edge := (i, j)} ∈ edges)
--     (λ _, false)
--     (λ _, {edge . edge := (j, i)} ∈ edges))

-- def decidable_nbhds_describe_edges (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : bool := 
--   smap.forall_keys (λ i, (@stree.option_forall ℕ (_) (λ j, 
--     decidable.lt_by_cases i j
--       (λ _, {edge . edge := (i, j)} ∈ edges)
--       (λ _, false)
--       (λ _, {edge . edge := (j, i)} ∈ edges))
--     ) (begin simp [decidable.lt_by_cases], apply_instance end) (_) (_) (_) (nbhds.to_map i)) nbhds

-- def edges_describe_nbhds (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : Prop :=
--   ∀ e : edge, e ∈ edges → e.edge.snd ∈ nbhds.to_map e.edge.fst

-- def decidable_edges_describe_nbhds (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : bool :=
--   stree.forall (λ e : edge, e.edge.snd ∈ nbhds.to_map e.edge.fst) edges

-- def describes_neighborhoods (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : Prop := 
-- nbhds_condition nbhds ∧ nbhds_describe_edges nbhds edges ∧ edges_describe_nbhds nbhds edges

-- def decidable_describes_neighborhoods (nbhds : tmap ℕ (tset ℕ)) (edges : tset edge) : bool := 
-- decidableNbhdsCondition nbhds ∧ decidable_nbhds_describe_edges nbhds edges ∧ decidable_edges_describe_nbhds nbhds edges



-- The definition of a finite graph that will represent the graphs that we import from House of Graphs
structure SimpleIrreflexiveGraph : Type :=
  (vertexSize : ℕ)
  (isVertex := fun (k : ℕ) => k < vertexSize)
  (edges : Tset Edge)
  (isEdge := fun (e : Edge) => (e.edge.fst < vertexSize) ∧ (e.edge.snd < vertexSize))
  (edgesCorrect : Stree.forall (fun e => (e.edge.fst < vertexSize) ∧ (e.edge.snd < vertexSize)) edges := by bool_reflect)
  (edgeSize : ℕ)
  (edgeSizeCorrect : edgeSize = edges.size)
  (neighborhoods : Tmap ℕ (Tset ℕ))
  (neighborhoodsCorrect : decidableNbhdsCondition neighborhoods = true)
  (minDegree : Option ℕ)
  (minDegreeCorrect : minDegree = (neighborhoods.map Tset.size).min?)
  (maxDegree : Option ℕ)
  (maxDegreeCorrect : maxDegree = (neighborhoods.map Tset.size).max?)
  (isRegular : Bool)
  (isRegularCorrect : isRegular = (minDegree = maxDegree))

@[reducible, simp]
instance SimpleIrreflexiveGraph.hasMem : Membership ℕ SimpleIrreflexiveGraph where
  mem := fun k g => g.isVertex k

def edgeRelation (G : SimpleIrreflexiveGraph) : ℕ → ℕ → Prop :=
  fun u v => lt_by_cases u v
    (fun _ => { edge := (u,v), src_lt_trg := by assumption } ∈ G.edges)
    (fun _ => False)
    (fun _ => { edge := (v,u), src_lt_trg := by assumption } ∈ G.edges)

    macro:max g:term:60 " [" u:term:60 " ~~ " v:term:60 "] " : term => `(edgeRelation $g $u $v)

def endpointIsVertex (G : SimpleIrreflexiveGraph) {u v : ℕ} :
  G[u ~~ v] -> G.isVertex u ∧ G.isVertex v := by
    intro e
    let moo := Stree.forallIsForall (fun e => (e.edge.fst < G.vertexSize) ∧ (e.edge.snd < G.vertexSize)) G.edges G.edgesCorrect
    apply lt_by_cases u v
    · sorry
    · sorry
    · sorry

def theEdge (g : SimpleIrreflexiveGraph) {u v : ℕ} :
  edgeRelation g u v → Edge :=
  by
    intro e
    apply lt_by_cases u v
    · intro uv
      exact Edge.mk (u, v)
    · intro uv
      simp [uv, edgeRelation, lt_by_cases] at e
    · intro uv
      exact Edge.mk (v, u)  

lemma edgeRelationIrreflexive {G : SimpleIrreflexiveGraph} : ∀ {v}, ¬ G[v ~~ v] := by
  intro v
  unfold edgeRelation
  simp [lt_by_cases]

lemma edgeRelationSymmetric {G : SimpleIrreflexiveGraph} :
  ∀ {u v}, G[u ~~ v] → G[v ~~ u] := by
  intros u v edge_uv
  apply lt_by_cases u v
  · intro h
    simp [edgeRelation, h, lt_by_cases, asymm h]
    simp [edgeRelation, h, lt_by_cases] at edge_uv
    exact edge_uv
  · intro h
    rw [h] at edge_uv
    have irr := @edgeRelationIrreflexive G v
    contradiction
  · intro h
    simp [edgeRelation, h, lt_by_cases]
    simp [edgeRelation, h, lt_by_cases, asymm h] at edge_uv
    exact edge_uv

lemma edgeRelationIsMem {G : SimpleIrreflexiveGraph} : 
  ∀ {u v} {uv : u < v}, G[u ~~ v] → { edge := (u, v), src_lt_trg := uv } ∈ G.edges := by
  intros u v uv euv
  simp [edgeRelation, lt_by_cases, uv] at euv
  exact euv
