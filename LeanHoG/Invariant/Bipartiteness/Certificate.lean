import Qq
import LeanHoG.JsonData
import LeanHoG.Edge
import LeanHoG.Graph
import LeanHoG.Invariant.Bipartiteness.Basic
import LeanHoG.Util.Quote
import LeanHoG.Util.RBSet

namespace LeanHoG

open Qq

/-- Construct a bipartiteness certificate from bipartiteness data -/
def bipartitenessCertificateOfData (G : Q(Graph)) (B : BipartitenessData) : Q(BipartitenessCertificate $G) :=
  have n : Q(Nat) := q(Graph.vertexSize $G)
  have convertToFin : Nat × Nat → Q(Fin $n × Fin 2) := fun (i,j) => q(($(finOfData n i), $(finOfData (Lean.mkRawNatLit 2) j)))
  have colorMap : Q(Std.RBMap (Graph.vertex $G) (Fin 2) Fin.instLinearOrderFin.compare) :=
    build_RBMap (B.color.map convertToFin) q(Fin.instLinearOrderFin)
  have color : Q(Graph.vertex $G → Fin 2) := q(fun v => Std.RBMap.findD $colorMap v 0)
  have vertex0 : Q(Graph.vertex $G) := finOfData n B.vertex0
  have vertex1 : Q(Graph.vertex $G) := finOfData n B.vertex1
  have edgeColor : Q(Std.RBSet.all (Graph.edgeTree $G) (fun e => $color e.fst ≠ $color e.snd) = true) := (q(Eq.refl true) : Lean.Expr)
  have vertex0Color : Q($color $vertex0 = 0) := (q(Eq.refl (0 : Fin 2)) : Lean.Expr)
  have vertex1Color : Q($color $vertex1 = 1) := (q(Eq.refl (1 : Fin 2)) : Lean.Expr)
  q(BipartitenessCertificate.mk
    $color
    $vertex0
    $vertex1
    (Graph.all_edges $G (fun e => $color e.fst ≠ $color e.snd) $edgeColor)
    $vertex0Color
    $vertex1Color
  )

end LeanHoG
