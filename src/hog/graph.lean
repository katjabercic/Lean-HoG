-- Custom definitions of graphs to work around some idiosyncracies of
-- graphs defined in mathlib.
import tactic
import .tactic
import .tree_representation
import .tree_set

open tree_set

-- set_option trace.class_instances true

structure simple_irreflexive_graph : Type :=
  (vertex_size : ℕ)
  (edges : tset Edge)
  (edge_size : ℕ)
  (edge_size_correct : edge_size = edges.size)
  -- (neighborhoods : list (ℕ × list ℕ))

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

-- def from_edge_list (n : ℕ) (edges : list (ℕ × ℕ)) : simple_irreflexive_graph :=
-- { vertex_size := n,
--   edge :=
--     (λ (i : fin n) (j : fin n), ¬ i = j ∧ (list.mem (i.val, j.val) edges ∨ list.mem (j.val, i.val) edges)),
--   edge_decidable := begin intros i j, apply_instance end,
--   irreflexive := begin intro i, tautology end,
--   symmetric := begin intros i j, tautology end,
--   edge_size := edges.length,
--   neighborhoods := []
-- }

-- def from_BST (n : ℕ) (tree : BST Edge) : simple_irreflexive_graph :=
-- { vertex_size := n,
--   edge :=
--     (λ (i : fin n) (j : fin n), ¬ i = j ∧ (BT.edge tree.tree i.val j.val)),
--   edge_decidable := begin intros i j, apply_instance end,
--   irreflexive := begin intro i, tautology end,
--   symmetric := begin intros i j h, split, tautology, cases h, apply BT.edge_symm, assumption end,
--   edge_size := tree.edge_size,
--   neighborhoods := BST.neighborhoods tree n
-- }

@[reducible]
def to_simple_graph (G : simple_irreflexive_graph) : simple_graph ℕ :=
{ simple_graph . 
  adj := edge_relation G,
  loopless := edge_relation_irreflexive,
  sym := edge_relation_symmetric
}

-- def edge_size (g : simple_irreflexive_graph) : ℕ :=
-- begin
--   haveI := g.edge_decidable,
--   exact fintype.card { e : fin g.vertex_size × fin g.vertex_size | e.fst < e.snd  ∧ g.edge e.fst e.snd }
-- end

-- class hog_edge_size (g : simple_irreflexive_graph) : Type :=
--   (edge_size_val : ℕ)
--   (edge_size_eq : edge_size g = edge_size_val . obviously)

-- noncomputable def max_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.max_degree (to_simple_graph g)

-- class hog_max_degree (g : simple_irreflexive_graph) : Type :=
--   (val : ℕ)
--   (mag_degree_eq : max_degree g = val . obviously)

-- noncomputable def min_degree (g : simple_irreflexive_graph) : ℕ := simple_graph.min_degree (to_simple_graph g)

-- class hog_min_degree (g : simple_irreflexive_graph) : Type :=
--   (val : ℕ)
--   (min_degree_eq : min_degree g = val . obviously)

-- class hog_regular (g : simple_irreflexive_graph) [max : hog_max_degree g] [min : hog_min_degree g] : Type :=
--   (hog_regular : max.val = min.val . obviously)