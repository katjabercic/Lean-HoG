import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.JsonData

namespace LeanHoG

/-- The neighbors of each vertex, indexed by vertex number. -/
def Graph.adjacencyList (G : Graph) : Array (Array Nat) :=
  G.edgeSet.foldl
    (fun adj e => (adj.modify e.fst.val (·.push e.snd.val)).modify e.snd.val (·.push e.fst.val))
    (Array.replicate G.vertexSize #[])

/-- Adjacency of two vertices given by their numbers, `false` when either is out of
    range. -/
def Graph.badjacentNat (G : Graph) (u v : Nat) : Bool :=
  if hu : u < G.vertexSize then
    if hv : v < G.vertexSize then G.badjacent ⟨u, hu⟩ ⟨v, hv⟩ else false
  else false

/-- A breadth-first search forest: one tree per connected component. `color` holds the
    parity of a vertex's distance from the root of its tree, `parent` its predecessor
    in that tree, with a root recorded as its own parent. -/
structure BFSForest where
  color : Array Nat
  parent : Array Nat
  visited : Array Bool

namespace BFSForest

/-- The forest on `n` vertices in which nothing has been visited yet. -/
def empty (n : Nat) : BFSForest where
  color := Array.replicate n 0
  parent := Array.replicate n 0
  visited := Array.replicate n false

/-- Grow the tree rooted at `root`, visiting every vertex reachable from it that the
    forest does not already hold, and coloring each by the parity of its distance
    from `root`. -/
def exploreFrom (adj : Array (Array Nat)) (root : Nat) (f : BFSForest) : BFSForest := Id.run do
  let mut f := { f with
    parent := f.parent.set! root root
    visited := f.visited.set! root true }
  let mut queue : Array Nat := #[root]
  let mut head : Nat := 0
  while head < queue.size do
    let u := queue[head]!
    head := head + 1
    for v in adj[u]! do
      unless f.visited[v]! do
        f := { color := f.color.set! v (1 - f.color[u]!)
               parent := f.parent.set! v u
               visited := f.visited.set! v true }
        queue := queue.push v
  return f

/-- The vertices from `v` up to the root of its tree, `v` first. -/
def ancestors (f : BFSForest) (v : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat
    | 0, v => [v]
    | fuel + 1, v =>
      let p := f.parent[v]!
      if p == v then [v] else v :: go fuel p
  go f.parent.size v

/-- The closed walk through `u`, the tree edges up to the deepest common ancestor of
    `u` and `v`, the tree edges back down to `v`, and the edge from `v` to `u`. It is
    listed by its vertices, starting at `u` and not repeating it at the end. `none`
    when `u` and `v` lie in different trees. -/
def closedWalkThrough (f : BFSForest) (u v : Nat) : Option (List Nat) :=
  let up := (f.ancestors u).reverse
  let vp := (f.ancestors v).reverse
  let shared := ((up.zip vp).takeWhile (fun p => p.fst == p.snd)).length
  if shared = 0 then none else some ((up.drop (shared - 1)).reverse ++ vp.drop shared)

end BFSForest

/-- A breadth-first search forest for `G`, rooted once in each connected component. -/
def Graph.bfsForest (G : Graph) : BFSForest := Id.run do
  let adj := G.adjacencyList
  let mut f := BFSForest.empty G.vertexSize
  for root in List.range G.vertexSize do
    unless f.visited[root]! do
      f := f.exploreFrom adj root
  return f

/-- An edge whose endpoints `color` colors alike, if there is one. -/
def Graph.monochromaticEdge (G : Graph) (color : Array Nat) : Option (Nat × Nat) :=
  G.edgeSet.foldl (init := none) fun found e =>
    match found with
    | some _ => found
    | none =>
      if color[e.fst.val]! == color[e.snd.val]! then some (e.fst.val, e.snd.val) else none

/-- Whether the vertices in `walk` are consecutively adjacent in `G`, the last is
    adjacent to the first, and there is an odd number of them. -/
def Graph.isOddClosedWalk (G : Graph) (walk : List Nat) : Bool :=
  match walk with
  | [] => false
  | v :: _ =>
    walk.length % 2 == 1 &&
      (walk.zip (walk.tail ++ [v])).all (fun p => G.badjacentNat p.fst p.snd)

/-- What a breadth-first search decides about the bipartiteness of a graph: a coloring
    of the vertices by the parity of their distance from the root of their component,
    or a closed walk of odd length. -/
inductive BipartiteSearchResult where
  | twoColoring (data : TwoColoringData)
  | oddClosedWalk (data : OddClosedWalkData)

/-- Decide bipartiteness of `G` by breadth-first search, returning the certificate for
    whichever answer it reaches.

    A coloring is returned only once `monochromaticEdge` has found no edge to refute
    it, and the odd closed walk is checked against the graph in the same way before it
    is returned. Soundness does not rest on either check: `TwoColoringOfData` and
    `OddClosedWalkOfData` prove every obligation by `Eq.refl` at `decide`, so the
    kernel rejects data that does not describe what it claims to. But it rejects it as
    a type mismatch inside a term the user never wrote, and it does so long after the
    command has reported success, so a search that went wrong is easier to read about
    here. -/
def Graph.searchBipartite (G : Graph) : Except String BipartiteSearchResult :=
  let forest := G.bfsForest
  match G.monochromaticEdge forest.color with
  | none =>
    .ok (.twoColoring ⟨(Array.range G.vertexSize).zip forest.color⟩)
  | some (u, v) =>
    match forest.closedWalkThrough u v with
    | none =>
      .error s!"the search colored the adjacent vertices {u} and {v} alike, but placed \
        them in different connected components"
    | some walk =>
      if G.isOddClosedWalk walk then
        .ok (.oddClosedWalk ⟨walk⟩)
      else
        .error s!"the search returned {walk}, which is not a closed walk of odd length \
          in the graph"

end LeanHoG
