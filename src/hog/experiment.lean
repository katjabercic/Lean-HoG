import .graph_invariant
import .hog
import init.logic

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

def petersen : hog.preadjacency
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



-- namespace tactic
-- namespace interactive
-- open expr tactic

-- setup_tactic_parser
  
-- -- t ← mathematica.run_command_on (λ s, "StringReplace[ " ++ s ++ ", { \"[\" -> \"{\", \"]\" -> \"}\", \"(\" -> \"{\", \")\" -> \"}\"}] // ToExpression" ) e',

-- meta def wololo (e : parse texpr) : tactic unit :=
-- do
--   e' ← i_to_expr e,
--   t ← mathematica.run_command_on (λ s, s ++ "// LeanForm // Activate") e',
--   ts ← tactic.to_expr t,
--   tactic.trace ts,
--   return ()


-- end interactive
-- end tactic

def neighborhoods_to_pred : hog.neighbor_relation → ℕ → ℕ → Prop
| [] := λ _ _, false
| (v :: vs) := 


def graph_from_neighborhoods : hog.neighbor_relation → simple_graph ℕ :=
sorry


def neighbors1 : hog.neighbor_relation := [(0, [4]), (1, [4]), (2,[3]), (3,[2,4]), (4,[0,1,3])]
-- [(0, 4), (1, 4), (2, 3), (3, 2), (3, 4), (4, 0), (4, 1), (4, 3)]
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

-- def graph1 := simple_graph.from_rel adj1
-- #check graph1

-- def graph1' : simple_graph ℕ := {
--   adj := irr adj1,
--   sym := symmetric_irr adj1,
--   loopless := loopless_irr adj1
-- }

-- def hog1 : hog.hog := {
--   neighborhoods := neighbors1,
--   preadjacency := adj1,
--   graph := graph1' 
-- }


def test : ∀ (k : fin 100), k.val + 1 = k.val + 1 :=
begin
  simp,
end

#print test
#check forall_congr
#check forall_congr_eq
#check trivial
#check forall_const

@[reducible]
def cow {p : Prop} [d : decidable p] : my_to_bool p = true → p := by simp

example: adj1 2 3 := 
begin
  simp, refl
end

example: ¬ adj1 2 2 := cow eq.refl

example:  ∀ x, ¬(restrict adj1 4 x x) := cow eq.refl
-- begin
--   simp, 
-- end



#reduce hog1
