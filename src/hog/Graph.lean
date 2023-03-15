import Mathlib.Order.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Prod.Lex
import Init.Prelude
import TreeSet
import TreeMap
import Tactic

open TreeSet
open TreeMap

-- The type of edges
structure Edge : Type :=
  edge        : Lex (Nat × Nat)
  src_lt_trg  : edge.fst < edge.snd := by bool_reflect

instance EdgeLinearOrder : LinearOrder Edge := 
  LinearOrder.lift' (fun (u : Edge) => u.edge) (fun u v H => by cases u; cases v; simp; assumption)

-- def nbhds_condition (nbhds : tmap ℕ (tset ℕ)) : Prop :=
--   ∀ i : ℕ, smap.contains_key i nbhds → (∀ j : ℕ, j ∈ nbhds.to_map i → i ∈ nbhds.to_map j)

-- theorem test (nbhds : Tmap ℕ (Tset ℕ)) : DecidablePred (fun j => i ∈ nbhds.toMap j) := by
--   intro j

def decidableNbhdsCondition (nbhds : Tmap ℕ (Tset ℕ)) : Bool := sorry
  -- Smap.forallKeys (fun i => Stree.optionForall (fun j => i ∈ nbhds.toMap j) (nbhds.toMap i)) nbhds

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
  (edges : Tset Edge)
  (edgeSize : ℕ)
  (edgeSizeCorrect : edgeSize = edges.size)
  (neighborhoods : Tmap ℕ (Tset ℕ))
  (neighborhoods_correct : decidableNbhdsCondition neighborhoods = tt)
