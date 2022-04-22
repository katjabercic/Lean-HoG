-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.
import tactic
import .tactic
import .tree_set

open tree_set

-- set_option trace.class_instances true

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edges : tset Edge)
  (edge_size : ℕ)
  (edge_size_correct : edge_size = edges.size)
  (neighborhoods : tmap ℕ (tset ℕ))


def neighborhoods_condition (nbhds : tmap ℕ (tset ℕ)) : Prop :=
  ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → i ∈ nbhds.to_map j)

-- def decidable_nbhds_condition (nbhds : tmap ℕ (tset ℕ)) : bool :=
--   smap.forall (λ t, stree.forall  ) nbhds

def nbhds_describe_edges (g : simple_irreflexive_graph) : Prop := 
  ∀ i : ℕ, ∀ j : ℕ, j ∈ g.neighborhoods.to_map i
  → decidable.lt_by_cases i j
    (λ _, {Edge . edge := (i, j)} ∈ g.edges)
    (λ _, false)
    (λ _, {Edge . edge := (j, i)} ∈ g.edges)

def edges_describe_nbhds (g : simple_irreflexive_graph) : Prop :=
  ∀ e : Edge, e ∈ g.edges → e.edge.snd ∈ g.neighborhoods.to_map e.edge.fst

def describes_neighborhoods (g : simple_irreflexive_graph) : Prop := nbhds_describe_edges g ∧ edges_describe_nbhds g


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