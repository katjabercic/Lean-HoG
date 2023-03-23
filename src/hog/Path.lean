import Graph
import ConnectedComponents
import TreeSet


-- -- [ ] Be able to define the functions on paths my pattern matching instead of having to use induction

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive Path {g : SimpleIrreflexiveGraph} : Fin g.vertexSize → Fin g.vertexSize → Type
| trivial (s : Fin g.vertexSize) : Path s s
| left (s t u : Fin g.vertexSize) : (edgeRelation g) s t → Path t u →  Path s u
| right (s t u : Fin g.vertexSize) : (edgeRelation g) t u → Path s t → Path s u

-- -- We probably want some kind of list-like notation for defining paths, i.e. < v₁, v₂, …, vₙ > or something
macro p:term ".~" next:term : term => `(Path.right $next $p)
macro next:term "~." p:term : term => `(Path.left $next $p)


def reversePath {g : SimpleIrreflexiveGraph} {s t : Fin g.vertexSize} :  Path s t → Path t s
  | .trivial s => .trivial s
  | .left s t u e p => Path.right u t s (edgeRelationSymmetric e) (reversePath p)
  | .right s t u e p => Path.left u t s (edgeRelationSymmetric e) (reversePath p)

macro p:term "↑" : term => `(reversePath $p)

def concatPath {g : SimpleIrreflexiveGraph} {s t u : Fin g.vertexSize} : Path s t → Path t u → Path s u := fun p q =>
  match p with
  | .trivial s => q
  | .left s v t e p' =>
    match q with
    | .trivial t => Path.left s v t e p'
    | .left t w u r q' => Path.left s v u e (concatPath (Path.right v t w r p') q')
    | .right t w u r q' => Path.left s v u e (Path.right v w u r (concatPath p' q'))
  | p' =>
    match q with
    | .trivial t => p'
    | .left t w u r q' => concatPath (Path.right s t w r p') q'
    | .right t w u r q' => Path.right s w u r (concatPath p' q')

macro p:term "+" q:term : term => `(concatPath $p $q)

def edgePath {g : SimpleIrreflexiveGraph} {s t : Fin g.vertexSize} : (edgeRelation g) s t → Path s t := fun e =>
  Path.left s t t e (Path.trivial t)


def length {g : SimpleIrreflexiveGraph} {s t : Fin g.vertexSize} : Path s t → ℕ
  | .trivial s => 0
  | .left s _ t e p' => length p' + 1
  | .right s _ t e p' => length p' + 1


-- The easy direction, just apply induction on the structure of path
lemma pathImpliesConnected {g : SimpleIrreflexiveGraph} {s t : Fin g.vertexSize} : Path s t → connected g s t
  | .trivial s => connectedRefl
  | .left s _ t e p' => (edgeConnected e) ⊕ (pathImpliesConnected p')
  | .right s _ t e p' => pathImpliesConnected p' ⊕ (edgeConnected e)


-- lemma witnessPathToRoot (w : numComponentsWitness) (s : Fin w.G.vertexSize) : Path s (w.root (w.c s)) := by
--   apply @foo (Fin w.G.vertexSize) (w.h) (fun v => path v (w.root (w.c v)))
--   { intros v H
--     have h := w.uniqueness_of_roots v H
--     rw [←h]
--     apply path.trivial
--   }
--   { intros v h
--     by_cases H : (0 < w.h v)
--     { let u := w.next v
--       have hyp := w.height_cond v H
--       have p : path u (w.root (w.c u)) := by apply h; cases hyp; exact hyp_right
--       have same_c : w.c u = w.c v := {by apply w.connectEdges, cases hyp, assumption}
--       rw [←same_c]
--       have q : path u v := { by apply edge_path, cases hyp, exact hyp_left }
--       exact (q ↑) + p
--     }
--     { simp at H
--       have h := w.uniqueness_of_roots v H
--       rw [←h]
--       apply path.trivial
--     }
--   }


-- lemma witness_to_path (w : num_components_witness) (s t : fin w.G.vertex_size) : connected w.G s t → path s t :=
-- begin
--   intro cst,
--   have equal_c : w.c s = w.c t := begin apply iff.mpr, apply witness_connected_condition, exact cst end,
--   have path_s_root : path s (w.root (w.c s)) := witness_path_to_root w s,
--   rw equal_c at path_s_root,
--   exact path_s_root + (witness_path_to_root w t ↑)
-- end