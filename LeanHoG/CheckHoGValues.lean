import Lean
import Qq

import LeanHoG.Graph
import LeanHoG.Invariant.Bipartite.Certificate
import LeanHoG.Invariant.ConnectedComponents.Certificate
import LeanHoG.Invariant.NeighborhoodMap.Certificate

import LeanHoG.RawHoG

import LeanHoG.Certificate
import LeanHoG.CertificateNames
import LeanHoG.JsonData

import LeanSAT
import LeanHoG.Invariant.HamiltonianPath.SatEncoding
import LeanHoG.Invariant.HamiltonianPath.Certificate

namespace LeanHoG

open Qq Lean

syntax (name := validateHoG) "#validate_hog " ident : command
/-- `#validate_hog G` checks for the existence of certificates of invariants and
    compares their values to the values in the database. Whenever the values match,
    It adds a lemma saying that they are equal.
-/

@[command_elab validateHoG]
unsafe def validateHoGImpl : Elab.Command.CommandElab
  | `(#validate_hog $g) => do
    let graphDecl ← Elab.resolveGlobalConstNoOverloadWithInfo g
    have graphQ : Q(Graph) := Expr.const graphDecl [] -- this needs to be `have`, not `let` (too much information otherwise)
    let graphName := g.getId

    let rawHoGName := RawHoG.name graphName
    have rawHoGQ : Q(RawHoG $graphQ) := mkConst rawHoGName []

    Elab.Command.liftCoreM <| addDecl <| .thmDecl {
      name := concatenateName graphName "hog_number_of_vertices_correct"
      levelParams := []
      type := q(some (Graph.vertexSize $graphQ) = (@RawHoG.toRawHoGData _ $rawHoGQ).numberOfVertices?)
      value := q(Eq.refl (some (Graph.vertexSize $graphQ)))
    }
    Elab.Command.liftCoreM <| addDecl <| .thmDecl {
      name := concatenateName graphName "hog_number_of_edges_correct"
      levelParams := []
      type := q(some (Graph.edgeSize $graphQ) = (@RawHoG.toRawHoGData _ $rawHoGQ).numberOfEdges?)
      value := q(Eq.refl (some (Graph.edgeSize $graphQ)))
    }

    let connectedComponentsCertificateName := ConnectedComponentsCertificate.name graphName
    if Environment.contains (← getEnv) connectedComponentsCertificateName then
      have _certQ : Q(ConnectedComponentsCertificate $graphQ) := Expr.const connectedComponentsCertificateName []
      Elab.Command.liftCoreM <| addDecl <| .thmDecl {
        name := concatenateName graphName "hog_number_of_components_correct"
        levelParams := []
        type := q(some (ConnectedComponentsCertificate.val $graphQ) = (@RawHoG.toRawHoGData _ $rawHoGQ).numberOfComponents?)
        value := q(Eq.refl (some (ConnectedComponentsCertificate.val $graphQ)))
      }

    -- The two bipartiteness certificates can not exist simultaneously.
    let twoColoringName := TwoColoring.name graphName
    if Environment.contains (← getEnv) twoColoringName then
      have _certQ : Q(TwoColoring $graphQ) := Expr.const twoColoringName []
      Elab.Command.liftCoreM <| addDecl <| .thmDecl {
        name := concatenateName graphName "hog_bipartite_correct"
        levelParams := []
        type := q(some (Graph.bipartite $graphQ) = (@RawHoG.toRawHoGData _ $rawHoGQ).bipartite?)
        value := q(Eq.refl (some (Graph.edgeSize $graphQ)))
      }
    let oddClosedWalkName := OddClosedWalk.name graphName
    if Environment.contains (← getEnv) oddClosedWalkName then
      have _certQ : Q(OddClosedWalk $graphQ) := Expr.const oddClosedWalkName []
      Elab.Command.liftCoreM <| addDecl <| .thmDecl {
        name := concatenateName graphName "hog_bipartite_correct"
        levelParams := []
        type := q(some (Graph.bipartite $graphQ) = (@RawHoG.toRawHoGData _ $rawHoGQ).bipartite?)
        value := q(Eq.refl (some (Graph.edgeSize $graphQ)))
      }

    logInfo "HoG values match the (loaded) certificates"

  | _ => Elab.throwUnsupportedSyntax

end LeanHoG
