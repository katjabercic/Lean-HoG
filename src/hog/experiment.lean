import .graph_invariant
import .hog
import init.logic

-- maybe too much is getting opened here
import tactic
open tactic
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident tk)

-- Complete graph (on however many vertices)
def complete_preadjacency : hog.preadjacency
| i j := true

-- cycle on 3 points
def cycle3 : hog.preadjacency
| 0 1 := tt
| 1 2 := tt
| 2 0 := tt
| _ _ := ff -- catch all case for false

-- cycle on n points
def cycle (n : ℕ) : hog.preadjacency
| i j := ((i + 1) % n = j)

def petersen_preadj : hog.preadjacency
-- outer cycle
| 0 1 := tt
| 1 2 := tt
| 2 3 := tt
| 3 4 := tt
| 4 0 := tt
-- the spikes
| 0 5 := tt
| 1 6 := tt
| 2 7 := tt
| 3 8 := tt
| 4 9 := tt
| 5 7 := tt
| 6 8 := tt
| 7 9 := tt
| 8 5 := tt
| 9 6 := tt
| _ _ := ff -- catch all case

-- auxiliary map which symmetrizes a preadjancency and removes the diagonal
def irreflexive_symmetric (f : ℕ → ℕ → bool) : ℕ → ℕ → bool
| i j := (i ≠ j) ∧ (f i j ∨ f j i)

-- an adjacency list is a finite list of pairs (i,j) with i < j that represents
-- neigbhors in a graph. It does not encode the graph, because it does
-- not contain information about the graph size (consider the empty list).
def adjacency_list := list (ℕ × ℕ)

-- Conversion between preadjancencies and adjancency lists

-- convert an adjacency list to a preadjancency
def from_adjacency_list (lst : adjacency_list) : hog.preadjacency :=
  λ i j, list.mem (i,j) lst

-- cycle on 4 elements
def C4 : hog.preadjacency := from_adjacency_list [(0,1), (1,2), (2,3), (3,0)]

-- We can generate the adjancency list but we need to provide the graph size,
def from_preadjacency (G : hog.preadjacency) (n : ℕ) : adjacency_list :=
  let G' := irreflexive_symmetric G in
  let triangle (n : ℕ) :=
    list.join
    $ list.map (λ j , list.map (λ i , (i , j)) $ list.range j)
    $ list.range n
  in
    list.filter (λ (p : ℕ × ℕ) , G' (prod.fst p) (prod.snd p)) (triangle n)

-- Petersen graph as adjancency list
-- #reduce from_preadjacency petersen 10
def adj_cyc_3 := from_preadjacency cycle3 3
#check adj_cyc_3

@[simp, reducible]
def adj1_bool : ℕ → ℕ → bool
| 0 4 := tt
| 1 4 := tt
| 2 3 := tt
| 3 2 := tt
| 3 4 := tt
| 4 0 := tt
| 4 1 := tt
| 4 3 := tt
| _ _ := ff

@[simp, reducible]
def adj1 : ℕ → ℕ → Prop := λ i j, adj1_bool i j = tt

@[reducible]
def restrict {α : Type} (f : ℕ → ℕ → α) (n : ℕ) : fin n → fin n → α :=
λ i j, f i.val j.val

@[reducible]
def my_to_bool (p : Prop) [h : decidable p] : bool :=
decidable.cases_on h (λ h₁, bool.ff) (λ h₂, bool.tt)

#check restrict adj1 17

def irr (f : ℕ → ℕ → Prop) : (ℕ → ℕ → Prop)
| i j := i ≠ j ∧ (f i j ∨ f j i)

lemma symmetric_irr (f : ℕ → ℕ → Prop) : symmetric (irr f) :=
λ x y h, ⟨ne.symm h.left, or.symm h.right⟩ 

lemma loopless_irr (f : ℕ → ℕ → Prop) : irreflexive (irr f) :=
λ x h, false_of_ne h.left


@[reducible]
def cow {p : Prop} [d : decidable p] : my_to_bool p = true → p := 
begin
  casesI d,
  { simp [my_to_bool] },
  { simp, exact d }
end

example: adj1 2 3 := 
begin
  simp, refl
end

example: adj1 1 4 := cow rfl
example: ¬ adj1 2 2 := cow rfl
example:  ∀ x, ¬(restrict adj1 4 x x) := cow rfl

@[reducible]
def my_adj := restrict adj1 4

example: simple_graph (fin 4) :=
 { adj := my_adj,
   sym := begin unfold symmetric, exact cow rfl end,
   loopless := begin unfold irreflexive, exact cow rfl end
 }


example: simple_graph (fin 4) :=
  simple_graph.mk
    (restrict adj1 4)
    (begin unfold symmetric, exact cow rfl end)
    (begin unfold irreflexive, exact cow rfl end)

meta def tactic.interactive.from_preadj (n : parse texpr) (_ : parse $ tk "with") (adj : parse texpr) : tactic unit :=
do { r ← i_to_expr_strict
                  ``(simple_graph.mk
                      (restrict (%%adj) %%n)
                      (begin unfold symmetric, exact cow rfl end)
                      (begin unfold irreflexive, exact cow rfl end) : simple_graph (fin %%n)
                  ),
     exact r
}

def my_first_graph := by from_preadj 4 with adj1

@[reducible]
def petersen_preadj_prop : ℕ → ℕ → Prop :=
λ i j, petersen_preadj i j = tt

def petersen : hog.hog :=
  { hog.hog . 
    number_of_vertices := 10,
    graph := by from_preadj 10 with adj1,
    number_of_vertices_eq_size := rfl,
    acyclic := option.none,
    bipartite := option.none,
    chromatic_index := option.none,
    chromatic_number := option.none,
    circumference := option.none,
    claw_free := option.none,
    clique_number := option.none,
    connected := option.none,
    diameter := option.none,
    edge_connectivity := option.none,
    eulerian := option.none,
    genus := option.none,
    girth := option.none,
    hamiltonian := option.none,
    independence_number := option.none,
    longest_induced_cycle := option.none,
    longest_induced_path := option.none,
    matching_number := option.none,
    maximum_degree := option.none,
    minimum_degree := option.none,
    minimum_dominating_set := option.none,
    number_of_components := option.none,
    number_of_edges := option.none,
    number_of_triangles := option.none,
    planar := option.none,
    radius := option.none,
    regular := option.none,
    vertex_connectivity := option.none,
  }