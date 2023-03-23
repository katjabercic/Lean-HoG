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

def symmPath {g : SimpleIrreflexiveGraph} {s t : Fin g.vertexSize} :  Path s t → Path t s
  | .trivial s => .trivial s
  | .left s t u e p => Path.right u t s (edgeRelationSymmetric e) (symmPath p)
  | .right s t u e p => Path.left u t s (edgeRelationSymmetric e) (symmPath p)
  

macro p:term "↑" : term => `(symmPath $p)

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