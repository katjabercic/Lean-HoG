import .decode
import .graph_invariant
import .hog
import .data.hog_data_001

-- We define a pre-adjancency map as a ℕ → ℕ → bool. There is no information about the size of the graph, so
-- effectively we are encoding countably infinite graphs.

def preadjacency := ℕ → ℕ → bool

-- Examples of preadjancency maps

-- Complete graph (on however many vertices)
def complete_preadjacency : preadjacency
| i j := true

-- cycle on 3 points
def cycle3 : preadjacency
| 0 1 := tt
| 1 2 := tt
| 2 0 := tt
| _ _ := ff -- catch all case for false

-- cycle on n points
def cycle (n : ℕ) : preadjacency
| i j := ((i + 1) % n = j)

def petersen : preadjacency
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
def from_adjacency_list (lst : adjacency_list) : preadjacency :=
  λ i j, list.mem (i,j) lst

-- cycle on 4 elements
def C4 : preadjacency := from_adjacency_list [(0,1), (1,2), (2,3), (3,0)]

-- We can generate the adjancency list but we need to provide the graph size,
def from_preadjacency (G : preadjacency) (n : ℕ) : adjacency_list :=
  let G' := irreflexive_symmetric G in
  let triangle (n : ℕ) :=
    list.join
    $ list.map (λ j , list.map (λ i , (i , j)) $ list.range j)
    $ list.range n
  in
    list.filter (λ (p : ℕ × ℕ) , G' (prod.fst p) (prod.snd p)) (triangle n)

-- Petersen graph as adjancency list
#reduce from_preadjacency petersen 10

-- "IsP@OkWHG" in HoG
#eval ((let (n, f) := hog.decode_graph6 "IheA@GUAo" in from_preadjacency f n) : list (ℕ × ℕ))

-- #eval ((let (n, f) := hog.decode_graph6 "IheA@GUAo" in from_preadjacency f n) : list (ℕ × ℕ))

-- Test the max_degree invariant
#check hog.to_simple_graph hog.hog00001

def g := hog.to_simple_graph hog.hog00001

-- #check graph_invariant.max_degree g
