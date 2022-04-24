import .graph
import .tree_set
--import .graph

--namespace combinatorial_map
open tree_set

--structure cycle {α : Type} [linear_order α] : Type :=
  --(carrier : tset α)
-- def next_in_tree (next : tmap ℕ ℕ) : next.
def walk (start : ℕ) (next : tmap ℕ ℕ) : ℕ → ℕ → Prop
| cur 0 := start = cur
| cur (n + 1) := 
  start ≠ cur ∧ 
  (match next.val_at cur with
  | none := false
  | some val := walk val n 
  end)

def is_cycle (next : tmap ℕ ℕ) : Prop :=
(match next with -- to start the walk we need to get some initial key
| (smap.empty _) := true
| (smap.leaf k _ _ _) := (
  match next.val_at k with
  | none := false -- this case is impossible - TODO : make the function reflect this fact
  | some val := walk k next val next.size
  end
)
| (smap.node k _ _ _) := 
 (
  match next.val_at k with
  | none := false -- this case is impossible - TODO : make the function reflect this fact
  | some val := walk k next val next.size
  end
)
end)

structure cycle : Type :=
  (next : tmap ℕ ℕ)
  (is_cyc : is_cycle next)

structure is_cycle_of (c : cycle) (t : tset ℕ) :=
  (sizes_match : smap.size (c.next) = t.size)
  (elements_match : t.forall (λ v, c.next.contains_key v))

def neighbours (G : simple_irreflexive_graph) : tmap ℕ (tset ℕ) :=
  sorry


structure combinatorial_map (G : simple_irreflexive_graph) : Type :=
  (neighbours : fin G.vertex_size → tset (fin (G.vertex_size)))

--def cycles := 

--end combinatorial_map
