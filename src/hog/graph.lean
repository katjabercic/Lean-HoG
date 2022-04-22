-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.
import tactic
import tactic.cache
import .tactic
import .tree_set
import .tree_map

open tree_set
open tree_map

-- The type of edges
structure Edge : Type :=
  (edge : lex ℕ ℕ)
  (src_lt_trg : edge.fst < edge.snd . obviously)

instance Edge_linear_order : linear_order Edge :=
  linear_order.lift (λ (u : Edge), u.edge) (λ u v H, begin cases u, cases v, simp, assumption end)

def nbhds_condition (nbhds : tmap ℕ (tset ℕ)) : Prop :=
  ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → i ∈ nbhds.to_map j)

def decidable_nbhds_condition (nbhds : tmap ℕ (tset ℕ)) : bool :=
  smap.forall_keys (λ i, stree.option_forall (λ j, i ∈ nbhds.to_map j) (nbhds.to_map i)) nbhds

def nbhds_describe_edges (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : Prop := 
  ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → decidable.lt_by_cases i j
    (λ _, {Edge . edge := (i, j)} ∈ edges)
    (λ _, false)
    (λ _, {Edge . edge := (j, i)} ∈ edges))

def decidable_nbhds_describe_edges (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : bool := 
  smap.forall_keys (λ i, (@stree.option_forall ℕ (_) (λ j, 
    decidable.lt_by_cases i j
      (λ _, {Edge . edge := (i, j)} ∈ edges)
      (λ _, false)
      (λ _, {Edge . edge := (j, i)} ∈ edges))
    ) (begin simp [decidable.lt_by_cases], apply_instance end) (_) (_) (_) (nbhds.to_map i)) nbhds

def edges_describe_nbhds (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : Prop :=
  ∀ e : Edge, e ∈ edges → e.edge.snd ∈ nbhds.to_map e.edge.fst

def decidable_edges_describe_nbhds (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : bool :=
  stree.forall (λ e : Edge, e.edge.snd ∈ nbhds.to_map e.edge.fst) edges

def describes_neighborhoods (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : Prop := 
nbhds_condition nbhds ∧ nbhds_describe_edges nbhds edges ∧ edges_describe_nbhds nbhds edges

def decidable_describes_neighborhoods (nbhds : tmap ℕ (tset ℕ)) (edges : tset Edge) : bool := 
decidable_nbhds_condition nbhds ∧ decidable_nbhds_describe_edges nbhds edges ∧ decidable_edges_describe_nbhds nbhds edges

-- The definition of a finite graph that will represent the graphs that we import from House of Graphs
structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edges : tset Edge)
  (edge_size : ℕ)
  (edge_size_correct : edge_size = edges.size)
  (neighborhoods : tmap ℕ (tset ℕ))
  (neighborhoods_correct : decidable_nbhds_condition neighborhoods = tt)


def edge_relation (G : simple_irreflexive_graph) : ℕ → ℕ → Prop :=
λ u v, decidable.lt_by_cases u v
  (λ _, {Edge . edge := (u, v)} ∈ G.edges)
  (λ _, false)
  (λ _, {Edge . edge := (v, u)} ∈ G.edges)

lemma edge_relation_irreflexive {G : simple_irreflexive_graph} : ∀ v, ¬ edge_relation G v v :=
begin 
  intros v,
  unfold edge_relation,
  simp [decidable.lt_by_cases]
end

lemma edge_relation_symmetric {G : simple_irreflexive_graph} :
  ∀ u v, edge_relation G u v → edge_relation G v u :=
begin
  intros u v edge_uv,
  apply decidable.lt_by_cases u v,
  { intro h,
    simp [edge_relation, h, decidable.lt_by_cases, asymm h],
    simp [edge_relation, h, decidable.lt_by_cases] at edge_uv,
    exact edge_uv
  },
  {
    intro h,
    rw h at edge_uv,
    have irreflexivity := edge_relation_irreflexive v,
    contradiction
  },
  {
    intro h,
    simp [edge_relation, h, decidable.lt_by_cases],
    simp [edge_relation, h, decidable.lt_by_cases, asymm h] at edge_uv,
    exact edge_uv
  }
end

lemma edge_relation_is_mem {G : simple_irreflexive_graph} : 
  Π u v (uv : u < v), edge_relation G u v → { Edge . edge := (u, v), src_lt_trg := uv } ∈ G.edges :=
begin
  intros u v uv euv,
  simp [edge_relation, decidable.lt_by_cases, uv] at euv,
  exact euv,
end

@[reducible]
def to_simple_graph (G : simple_irreflexive_graph) : simple_graph ℕ :=
{ simple_graph . 
  adj := edge_relation G,
  loopless := edge_relation_irreflexive,
  sym := edge_relation_symmetric
}
