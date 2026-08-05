import LeanHoG.LoadGraph

/-!
# Tests for the graph6 codec

`#guard` fails elaboration when its argument evaluates to `false`, so
`lake build Graph6Tests` is the whole test run.

The strings in `hogCanonicalForms` are the `canonicalForm` fields of the graphs
in `graphs/`, which HoG states in the same vertex labelling as the `edges` field
of the same file. They serve both as round-trip inputs and, against the loaded
JSON, as a check on the decoded edge set.
-/

namespace LeanHoG

/-- Whether `decode` accepts `s` and `encodeData` returns it unchanged. -/
def roundTrips (s : String) : Bool :=
  match Graph6.decode s with
  | .ok data => Graph6.encodeData data == s
  | .error _ => false

/-- Whether `decode` rejects `s`. -/
def rejects (s : String) : Bool :=
  match Graph6.decode s with
  | .ok _ => false
  | .error _ => true

/-- The vertex count and edge list `decode` produces, or `none` on failure. -/
def decoded (s : String) : Option (Nat × List (Nat × Nat)) :=
  match Graph6.decode s with
  | .ok data => some (data.vertexSize, data.edges.toList)
  | .error _ => none

/-- The edges of `G` as pairs of vertex numbers, in the order `edgeSet` holds them. -/
def edgePairs (G : Graph) : List (Nat × Nat) :=
  G.edgeSet.foldr (fun e acc => (e.fst.val, e.snd.val) :: acc) []

/-- Whether the pairs strictly increase lexicographically. -/
def lexIncreasing : List (Nat × Nat) → Bool
  | [] | [_] => true
  | a :: b :: rest =>
    (a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) && lexIncreasing (b :: rest)

def hogCanonicalForms : List String :=
  [ "Ms??OHGP?ccKEOH_?"
  , "}???????????????????????????????B???CO?@C??A_??I???K???@C???C_???S???C_???@?_???`???GG????`????AA????_O?????o????B??????B?????@G?????C_?????`?????OO?????AA?????AA?????@@????A??C????G??G????_?A?????_?@????????C??A_g??@??@OS???A_KO?????S?M??????NG???????qo????????a_a??????CSCC??????KGP??????@H?g????????Oco???????_Z???"
  , "Z~~vnZjvUtw~nSmis{{k~a^||QBtQJNHLU[VQ^BxkFnDK\\zEEvn@Tn^_Tn^w"
  , "L@GOOGA?GAG@_C"
  , "E}lw"
  , "F???G"
  , "UKb?GGGA@fi]Uog?S??G^@KwBp_Fb?Fb?w?^U?Fo"
  , "XcG_COOK_G?DAA@G_oOCQQ@@@o??i@?K?@?x?oAO_@kgD?UF_@o"
  , "D^{"
  , "X`Ic?dA??O???POO@A__PACc?Z@CA_HGGCa_@N??cIPGJ?We??{"
  , "IsP@OkWHG"
  , "\\_?O__AGP?@GACHG?qaCAaAP?_C?K?AT?G?E?@`?Ho_GC??CA?L??F`?w?EdO?AEK??^?" ]

/-! ## Round trips over the twelve HoG canonical forms -/

#guard hogCanonicalForms.length == 12
#guard hogCanonicalForms.all roundTrips

/-! ## The decoded graph agrees with the JSON of the same graph -/

load_graph hog_660 "graphs/660.json"
load_graph_from_g6 g6_660 "IsP@OkWHG"

#guard hog_660.vertexSize == g6_660.vertexSize
#guard edgePairs hog_660 == edgePairs g6_660
#guard hog_660.toGraph6 == "IsP@OkWHG"

load_graph hog_1030 "graphs/1030.json"
load_graph_from_g6 g6_1030 "}???????????????????????????????B???CO?@C??A_??I???K???@C???C_???S???C_???@?_???`???GG????`????AA????_O?????o????B??????B?????@G?????C_?????`?????OO?????AA?????AA?????@@????A??C????G??G????_?A?????_?@????????C??A_g??@??@OS???A_KO?????S?M??????NG???????qo????????a_a??????CSCC??????KGP??????@H?g????????Oco???????_Z???"

#guard hog_1030.vertexSize == 62
#guard edgePairs hog_1030 == edgePairs g6_1030

/-! ## Decoded edges are lexicographically ordered, as `graphOfData` requires -/

#guard lexIncreasing (edgePairs g6_660)
#guard lexIncreasing (edgePairs g6_1030)

/-! ## Small graphs, by hand -/

#guard decoded "?" == some (0, [])
#guard decoded "@" == some (1, [])
#guard decoded "A?" == some (2, [])
#guard decoded "A_" == some (2, [(0, 1)])
#guard decoded "D^{" == some (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)])
#guard decoded "F???G" == some (7, [(5, 6)])

/-! ## The optional header and surrounding whitespace -/

#guard decoded ">>graph6<<D^{" == decoded "D^{"
#guard decoded " \tD^{\n" == decoded "D^{"
#guard decoded ">>graph6<< D^{ " == decoded "D^{"

/-! ## Vertex counts needing the wide `N(n)` forms

No HoG example exceeds 62 vertices, so the `~` and `~~` branches are exercised
by encoding paths of the relevant sizes.
-/

/-- The path on `n` vertices. -/
def pathData (n : Nat) : GraphData :=
  { vertexSize := n, edges := ((List.range (n - 1)).map (fun i => (i, i + 1))).toArray }

#guard Graph6.encodeVertexCount 62 == "}"
#guard Graph6.encodeVertexCount 63 == "~??~"
#guard Graph6.encodeVertexCount 258047 == "~}~~"
#guard Graph6.encodeVertexCount 258048 == "~~???~??"

#guard roundTrips (Graph6.encodeData (pathData 62))
#guard roundTrips (Graph6.encodeData (pathData 63))
#guard roundTrips (Graph6.encodeData (pathData 70))
#guard decoded (Graph6.encodeData (pathData 70)) == some (70, (pathData 70).edges.toList)

/-! ## Rejected input -/

#guard rejects ""
#guard rejects "D^"      -- one byte of adjacency data short
#guard rejects "D^{{"    -- one byte too many
#guard rejects "D^,"     -- ',' is below '?'
#guard rejects "Dé{"     -- not ASCII
#guard rejects "~"       -- truncated wide vertex count
#guard rejects "~??"     -- truncated 18-bit vertex count
#guard rejects "~~?????" -- truncated 36-bit vertex count

/-! ## Loading a whole graph6 file -/

load_graphs_from_g6_file Sample "examples/hog-sample.g6"

#guard Sample_0.vertexSize == 10
#guard Sample_1.vertexSize == 6
#guard Sample_2.vertexSize == 5
#guard Sample_3.vertexSize == 7
#guard edgePairs Sample_0 == edgePairs hog_660
#guard Sample_0.toGraph6 == "IsP@OkWHG"
#guard Sample_1.toGraph6 == "E}lw"
#guard Sample_2.toGraph6 == "D^{"
#guard Sample_3.toGraph6 == "F???G"

end LeanHoG
