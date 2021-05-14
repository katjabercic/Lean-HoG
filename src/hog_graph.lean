-- We define a pre-adjancency map as a ℕ → ℕ → bool. There is no information about the size of the graph, so
-- effectively we are encoding countably infinite graphs.

def preadjacency := ℕ → ℕ → bool

-- auxiliary map which symmetrizes a preadjancency and removes the diagonal
def irreflexive_symmetric (f : ℕ → ℕ → bool) : ℕ → ℕ → bool
| i j := (i ≠ j) ∧ (f i j ∨ f j i)

-- an adjacency list is a finite list of pairs (i,j) with i < j that represents
-- neigbhors in a graph. It does not encode the graph, because it does
-- not contain information about the graph size (consider the empty list).
def adjacency_list := list (ℕ × ℕ)

-- We can generate the adjancency list but we need to provide the graph size,
def from_preadjacency (G : preadjacency) (n : ℕ) : adjacency_list :=
  let G' := irreflexive_symmetric G in
  let triangle (n : ℕ) :=
    list.join
    $ list.map (λ j , list.map (λ i , (i , j)) $ list.range j)
    $ list.range n
  in
    list.filter (λ (p : ℕ × ℕ) , G' (prod.fst p) (prod.snd p)) (triangle n)

-- convert an adjacency list to a preadjancency
def from_adjacency_list (lst : adjacency_list) : preadjacency :=
  λ i j, list.mem (i,j) lst