import Lean
import Qq
import Lean.Data.Json.Basic
import LeanHoG.LoadGraph
import LeanHoG.Widgets
import LeanHoG.Util.IO
import LeanHoG.Options

import ProofWidgets.Component.HtmlDisplay

namespace LeanHoG

open scoped ProofWidgets.Jsx
open Lean Widget Elab Command Term Meta Qq

inductive BoolInvariant where
  | Acyclic
  | Bipartite
  | Connected
  | ClawFree
  | Eulerian
  | Hamiltonian
  | Hypohamiltonian
  | Hypotraceable
  | Planar
  | Regular
  | Traceable
  | TwinFree
deriving Repr, Hashable

inductive NumericalInvariant where
  | AlgebraicConnectivity
  | AverageDegree
  | Index
  | LaplacianLargestEigenvalue
  | SecondLargestEigenvalue
  | SmallestEigenvalue
deriving Repr, Hashable

inductive IntegralInvariant
  | ChromaticIndex
  | ChromaticNumber
  | Circumference
  | CliqueNumber
  | Degeneracy
  | Density
  | Diameter
  | DominationNumber
  | EdgeConnectivity
  | FeedbackVertexSetNumber
  | Genus
  | Girth
  | GroupSize
  | IndependenceNumber
  | LengthOfLongestInducedCycle
  | LengthOfLongestInducedPath
  | LengthOfLongestPath
  | MatchingNumber
  | MaximumDegree
  | MinimumDegree
  | NumberOfComponents
  | NumberOfEdges
  | NumberOfSpanningTrees
  | NumberOfTriangles
  | NumberOfVertexOrbits
  | NumberOfVertices
  | NumberOfZeroEigenvalues
  | Radius
  | Treewidth
  | VertexConnectivity
  | VertexCoverNumber
deriving Repr, Hashable

inductive Invariant where
  | BoolInvariant : BoolInvariant → Invariant
  | NumericalInvariant : NumericalInvariant → Invariant
  | IntegralInvariant : IntegralInvariant → Invariant
deriving Repr, Hashable

def boolInvariantToId : BoolInvariant → Nat
  | .Acyclic => 1
  | .Bipartite => 3
  | .Connected => 6
  | .ClawFree => 33
  | .Eulerian => 28
  | .Hamiltonian => 29
  | .Hypohamiltonian => 41
  | .Hypotraceable => 42
  | .Planar => 36
  | .Regular => 18
  | .Traceable => 40
  | .TwinFree => 46

def numericalInvariantToId : NumericalInvariant → Nat
  | .AlgebraicConnectivity => 19
  | .AverageDegree => 2
  | .Index => 21
  | .LaplacianLargestEigenvalue => 22
  | .SecondLargestEigenvalue => 23
  | .SmallestEigenvalue => 24

def integralInvariantToId : IntegralInvariant → Nat
  | .ChromaticIndex => 20
  | .ChromaticNumber => 4
  | .Circumference => 35
  | .CliqueNumber => 5
  | .Degeneracy => 48
  | .Density => 34
  | .Diameter => 7
  | .DominationNumber => 13
  | .EdgeConnectivity => 8
  | .FeedbackVertexSetNumber => 47
  | .Genus => 32
  | .Girth => 9
  | .GroupSize => 37
  | .IndependenceNumber => 18
  | .LengthOfLongestInducedCycle => 31
  | .LengthOfLongestInducedPath => 25
  | .LengthOfLongestPath => 48
  | .MatchingNumber => 11
  | .MaximumDegree => 10
  | .MinimumDegree => 12
  | .NumberOfComponents => 26
  | .NumberOfEdges => 14
  | .NumberOfSpanningTrees => 43
  | .NumberOfTriangles => 27
  | .NumberOfVertexOrbits => 38
  | .NumberOfVertices => 15
  | .NumberOfZeroEigenvalues => 44
  | .Radius => 16
  | .Treewidth => 39
  | .VertexConnectivity => 30
  | .VertexCoverNumber => 45

def Invariant.toId : Invariant → Nat
  | .BoolInvariant inv => boolInvariantToId inv
  | .NumericalInvariant inv => numericalInvariantToId inv
  | .IntegralInvariant inv => integralInvariantToId inv

instance : Hashable Float where
  hash x := hash (Float.toString x)

def Invariant.valType : Invariant → Type
  | BoolInvariant _ => Bool
  | NumericalInvariant _ => Float
  | IntegralInvariant _ => Int

inductive ComparisonOp where
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
deriving Repr, Hashable

instance : ToString ComparisonOp where
  toString op :=
  match op with
  | .Eq => "EQ"
  | .Ne => "NE"
  | .Lt => "LT"
  | .Le => "LE"
  | .Gt => "GT"
  | .Ge => "GE"

structure BoolEnquiry where
  inv : BoolInvariant
  val : Bool
deriving Repr, Hashable

structure NumericalEnquiry where
  inv : NumericalInvariant
  op : ComparisonOp
  val : Float
deriving Repr, Hashable

structure IntegralEnquiry where
  inv : IntegralInvariant
  op : ComparisonOp
  val : Int
deriving Repr, Hashable

inductive HoGEnquiry where
  | BoolEnquiry : BoolEnquiry → HoGEnquiry
  | NumericalEnquiry : NumericalEnquiry → HoGEnquiry
  | IntegralEnquiry : IntegralEnquiry → HoGEnquiry
deriving Repr, Hashable

structure InvariantQuery where
  invariantId : Nat
  operator : String
  value : Float
deriving Lean.ToJson, Hashable

structure GraphClassQuery where
  invariantId : Nat
  hasClass : Bool
deriving Lean.ToJson, Hashable

structure HoGQuery where
  invariantEnquiries : List InvariantQuery
  invariantRangeEnquiries : List Int := []
  interestingInvariantEnquiries : List Int := []
  graphClassEnquiries : List GraphClassQuery
  invariantParityEnquiries : List Int := []
  textEnquiries : List String := []
  formulaEnquiries : List String := []
  mostRecent : Int := -1
  mostPopular : Int := -1
  subgraphEnquiries : List Int := []
deriving Lean.ToJson, Hashable

def boolInvariantToQuery : BoolInvariant → Bool → GraphClassQuery
  | .Acyclic, b => ⟨(Invariant.BoolInvariant .Acyclic).toId, b⟩
  | .Bipartite, b => ⟨(Invariant.BoolInvariant .Bipartite).toId, b⟩
  | .Connected, b => ⟨(Invariant.BoolInvariant .Connected).toId, b⟩
  | .ClawFree, b => ⟨(Invariant.BoolInvariant .ClawFree).toId, b⟩
  | .Eulerian, b => ⟨(Invariant.BoolInvariant .Eulerian).toId, b⟩
  | .Hamiltonian, b => ⟨(Invariant.BoolInvariant .Hamiltonian).toId, b⟩
  | .Hypohamiltonian, b => ⟨(Invariant.BoolInvariant .Hypohamiltonian).toId, b⟩
  | .Hypotraceable, b => ⟨(Invariant.BoolInvariant .Hypotraceable).toId, b⟩
  | .Planar, b => ⟨(Invariant.BoolInvariant .Planar).toId, b⟩
  | .Regular, b => ⟨(Invariant.BoolInvariant .Regular).toId, b⟩
  | .Traceable, b => ⟨(Invariant.BoolInvariant .Traceable).toId, b⟩
  | .TwinFree, b => ⟨(Invariant.BoolInvariant .TwinFree).toId, b⟩

def numericalInvariantToQuery : NumericalInvariant → ComparisonOp → Float → InvariantQuery
  | .AlgebraicConnectivity, op, x => ⟨(Invariant.NumericalInvariant .AlgebraicConnectivity).toId, toString op, x⟩
  | .AverageDegree, op, x => ⟨(Invariant.NumericalInvariant .AverageDegree).toId, toString op, x⟩
  | .Index, op, x => ⟨(Invariant.NumericalInvariant .Index).toId, toString op, x⟩
  | .LaplacianLargestEigenvalue, op, x => ⟨(Invariant.NumericalInvariant .LaplacianLargestEigenvalue).toId, toString op, x⟩
  | .SecondLargestEigenvalue, op, x => ⟨(Invariant.NumericalInvariant .SecondLargestEigenvalue).toId, toString op, x⟩
  | .SmallestEigenvalue, op, x => ⟨(Invariant.NumericalInvariant .SmallestEigenvalue).toId, toString op, x⟩

def integralInvariantToQuery : IntegralInvariant → ComparisonOp → Int → InvariantQuery
  | .ChromaticIndex, op, n => ⟨(Invariant.IntegralInvariant .ChromaticIndex).toId, toString op, .ofInt n⟩
  | .ChromaticNumber, op, n => ⟨(Invariant.IntegralInvariant .ChromaticNumber).toId, toString op, .ofInt n⟩
  | .Circumference, op, n => ⟨(Invariant.IntegralInvariant .Circumference).toId, toString op, .ofInt n⟩
  | .CliqueNumber, op, n => ⟨(Invariant.IntegralInvariant .CliqueNumber).toId, toString op, .ofInt n⟩
  | .Degeneracy, op, n => ⟨(Invariant.IntegralInvariant .Degeneracy).toId, toString op, .ofInt n⟩
  | .Density, op, n => ⟨(Invariant.IntegralInvariant .Density).toId, toString op, .ofInt n⟩
  | .Diameter, op, n => ⟨(Invariant.IntegralInvariant .Diameter).toId, toString op, .ofInt n⟩
  | .DominationNumber, op, n => ⟨(Invariant.IntegralInvariant .DominationNumber).toId, toString op, .ofInt n⟩
  | .EdgeConnectivity, op, n => ⟨(Invariant.IntegralInvariant .EdgeConnectivity).toId, toString op, .ofInt n⟩
  | .FeedbackVertexSetNumber, op, n => ⟨(Invariant.IntegralInvariant .FeedbackVertexSetNumber).toId, toString op, .ofInt n⟩
  | .Genus, op, n => ⟨(Invariant.IntegralInvariant .Genus).toId, toString op, .ofInt n⟩
  | .Girth, op, n => ⟨(Invariant.IntegralInvariant .Girth).toId, toString op, .ofInt n⟩
  | .GroupSize, op, n => ⟨(Invariant.IntegralInvariant .GroupSize).toId, toString op, .ofInt n⟩
  | .IndependenceNumber, op, n => ⟨(Invariant.IntegralInvariant .IndependenceNumber).toId, toString op, .ofInt n⟩
  | .LengthOfLongestInducedCycle, op, n => ⟨(Invariant.IntegralInvariant .LengthOfLongestInducedCycle).toId, toString op, .ofInt n⟩
  | .LengthOfLongestInducedPath, op, n => ⟨(Invariant.IntegralInvariant .LengthOfLongestInducedPath).toId, toString op, .ofInt n⟩
  | .LengthOfLongestPath, op, n => ⟨(Invariant.IntegralInvariant .LengthOfLongestPath).toId, toString op, .ofInt n⟩
  | .MatchingNumber, op, n => ⟨(Invariant.IntegralInvariant .MatchingNumber).toId, toString op, .ofInt n⟩
  | .MaximumDegree, op, n => ⟨(Invariant.IntegralInvariant .MaximumDegree).toId, toString op, .ofInt n⟩
  | .MinimumDegree, op, n => ⟨(Invariant.IntegralInvariant .MinimumDegree).toId, toString op, .ofInt n⟩
  | .NumberOfComponents, op, n => ⟨(Invariant.IntegralInvariant .NumberOfComponents).toId, toString op, .ofInt n⟩
  | .NumberOfEdges, op, n => ⟨(Invariant.IntegralInvariant .NumberOfEdges).toId, toString op, .ofInt n⟩
  | .NumberOfSpanningTrees, op, n => ⟨(Invariant.IntegralInvariant .NumberOfSpanningTrees).toId, toString op, .ofInt n⟩
  | .NumberOfTriangles, op, n => ⟨(Invariant.IntegralInvariant .NumberOfTriangles).toId, toString op, .ofInt n⟩
  | .NumberOfVertexOrbits, op, n => ⟨(Invariant.IntegralInvariant .NumberOfVertexOrbits).toId, toString op, .ofInt n⟩
  | .NumberOfVertices, op, n => ⟨(Invariant.IntegralInvariant .NumberOfVertices).toId, toString op, .ofInt n⟩
  | .NumberOfZeroEigenvalues, op, n => ⟨(Invariant.IntegralInvariant .NumberOfZeroEigenvalues).toId, toString op, .ofInt n⟩
  | .Radius, op, n => ⟨(Invariant.IntegralInvariant .Radius).toId, toString op, .ofInt n⟩
  | .Treewidth, op, n => ⟨(Invariant.IntegralInvariant .Treewidth).toId, toString op, .ofInt n⟩
  | .VertexConnectivity, op, n => ⟨(Invariant.IntegralInvariant .VertexConnectivity).toId, toString op, .ofInt n⟩
  | .VertexCoverNumber, op, n => ⟨(Invariant.IntegralInvariant .VertexCoverNumber).toId, toString op, .ofInt n⟩

abbrev QueryState := List InvariantQuery × List GraphClassQuery

structure ConstructedQuery where
  query : Json
  hash : UInt64

structure Queries where
  queries : List ConstructedQuery

def Queries.hash : Queries → UInt64 := fun ⟨qs⟩ =>
  let rec helper : List ConstructedQuery → UInt64
  | [] => 0
  | q :: qs => mixHash q.hash (helper qs)
  helper qs

open Lean in
def HoGQuery.build : List HoGEnquiry → ConstructedQuery := fun q =>
  let rec helper : List HoGEnquiry → StateM QueryState HoGQuery
  | [] => do
    let (invq,gcq) ← get
    return { invariantEnquiries := invq, graphClassEnquiries := gcq }
  | .BoolEnquiry ⟨.Bipartite, b⟩ :: es => do
    let (invq,gcq) ← get
    set (invq, ⟨(Invariant.BoolInvariant .Bipartite).toId, b⟩ :: gcq)
    helper es
  | .BoolEnquiry ⟨inv, b⟩ :: es => do
    let (invq,gcq) ← get
    set (invq, boolInvariantToQuery inv b :: gcq)
    helper es
  | .NumericalEnquiry ⟨inv, op, x⟩ :: es => do
    let (invq,gcq) ← get
    set (numericalInvariantToQuery inv op x :: invq, gcq)
    helper es
  | .IntegralEnquiry ⟨inv, op, n⟩ :: es => do
    let (invq,gcq) ← get
    set (integralInvariantToQuery inv op n :: invq, gcq)
    helper es

  let (j, _) := helper q ([],[])
  ⟨toJson j, hash j⟩

def distributeLeft {α : Type} : List α → List (List α) → List (List α)
  | _, [] => []
  | q, q' :: qs' => List.append q q' :: distributeLeft q qs'

def distribute {α : Type} : List (List α) → List (List α) → List (List α)
  | _, [] => []
  | [], _ => []
  | q :: qs, qs' =>
    let foo := distributeLeft q qs'
    List.append foo (distribute qs qs')

declare_syntax_cat boolean_invariant

syntax "acyclic" : boolean_invariant
syntax "bipartite" : boolean_invariant
syntax "connected" : boolean_invariant
syntax "clawFree" : boolean_invariant
syntax "eulerian" : boolean_invariant
syntax "hamiltonian" : boolean_invariant
syntax "hypohamiltonian" : boolean_invariant
syntax "hypotraceable" : boolean_invariant
syntax "planar" : boolean_invariant
syntax "regular" : boolean_invariant
syntax "traceable" : boolean_invariant
syntax "twinFree" : boolean_invariant

declare_syntax_cat integral_invariant

syntax "chromaticIndex" : integral_invariant
syntax "chromaticNumber" : integral_invariant
syntax "circumference" : integral_invariant
syntax "cliqueNumber" : integral_invariant
syntax "degeneracy" : integral_invariant
syntax "density" : integral_invariant
syntax "diameter" : integral_invariant
syntax "dominationNumber" : integral_invariant
syntax "edgeConnectivity" : integral_invariant
syntax "feedbackVertexSetNumber" : integral_invariant
syntax "genus" : integral_invariant
syntax "girth" : integral_invariant
syntax "groupSize" : integral_invariant
syntax "independenceNumber" : integral_invariant
syntax "lengthOfLongestInducedCycle" : integral_invariant
syntax "lengthOfLongestInducedPath" : integral_invariant
syntax "lengthOfLongestPath" : integral_invariant
syntax "matchingNumber" : integral_invariant
syntax "maximumDegree" : integral_invariant
syntax "minimumDegree" : integral_invariant
syntax "numberOfComponents" : integral_invariant
syntax "numberOfEdges" : integral_invariant
syntax "numberOfSpanningTrees" : integral_invariant
syntax "numberOfTriangles" : integral_invariant
syntax "numberOfVertexOrbits" : integral_invariant
syntax "numberOfVertices" : integral_invariant
syntax "numberOfZeroEigenvalues" : integral_invariant
syntax "radius" : integral_invariant
syntax "treewidth" : integral_invariant
syntax "vertexConnectivity" : integral_invariant
syntax "vertexCoverNumber" : integral_invariant

declare_syntax_cat numerical_invariant

syntax "algebraicConnectivity" : numerical_invariant
syntax "averageDegree" : numerical_invariant
syntax "index" : numerical_invariant
syntax "laplacianLargestEigenvalue" : numerical_invariant
syntax "secondLargestEigenvalue" : numerical_invariant
syntax "smallestEigenvalue" : numerical_invariant

declare_syntax_cat comparison_invariant

syntax numerical_invariant : comparison_invariant
syntax integral_invariant : comparison_invariant

declare_syntax_cat operation
syntax " = " : operation
syntax " < " : operation
syntax " != ": operation
syntax " > " : operation
syntax " <= " : operation
syntax " >= " : operation
syntax "op!{" operation "}" : term

macro_rules
  | `(op!{=}) => `(ComparisonOp.Eq)
  | `(op!{<}) => `(ComparisonOp.Lt)
  | `(op!{!=}) => `(ComparisonOp.Ne)
  | `(op!{>}) => `(ComparisonOp.Gt)
  | `(op!{<=}) => `(ComparisonOp.Le)
  | `(op!{>=}) => `(ComparisonOp.Ge)

declare_syntax_cat hog_query
syntax (name := hog) "hog{ " hog_query " }" : term
syntax:40 boolean_invariant:41 " = " term:40 : hog_query
syntax:40 comparison_invariant:41 operation term:40 : hog_query
syntax:35 hog_query:36 " ∧ " hog_query:35 : hog_query
syntax:30 hog_query:31 " ∨ " hog_query:30 : hog_query
syntax:max "(" hog_query ")" : hog_query

@[macro hog] def hogQueryImpl : Macro
  -- Boolean invariants
  | `(hog{bipartite = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Bipartite, $b⟩]])
  | `(hog{acyclic = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Acyclic, $b ⟩]])
  | `(hog{connected = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Connected, $b ⟩]])
  | `(hog{clawFree = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.ClawFree, $b ⟩]])
  | `(hog{eulerian = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Eulerian, $b ⟩]])
  | `(hog{hamiltonian = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Hamiltonian, $b ⟩]])
  | `(hog{hypohamiltonian = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Hypohamiltonian, $b ⟩]])
  | `(hog{hypotraceable = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Hypotraceable, $b ⟩]])
  | `(hog{planar = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Planar, $b ⟩]])
  | `(hog{regular = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Regular, $b ⟩]])
  | `(hog{traceable = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.Traceable, $b ⟩]])
  | `(hog{twinFree = $b}) => `([[HoGEnquiry.BoolEnquiry ⟨.TwinFree, $b ⟩]])

  -- Numerical invariants
  | `(hog{algebraicConnectivity $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.AlgebraicConnectivity, op!{$op}, $x⟩]])
  | `(hog{averageDegree $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.AverageDegree, op!{$op}, $x⟩]])
  | `(hog{index $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.Index, op!{$op}, $x⟩]])
  | `(hog{laplacianLargestEigenvalue $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.LaplacianLargestEigenvalue, op!{$op}, $x⟩]])
  | `(hog{secondLargestEigenvalue $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.SecondLargestEigenvalue, op!{$op}, $x⟩]])
  | `(hog{smallestEigenvalue $op $x}) => `([[HoGEnquiry.NumericalEnquiry ⟨.SmallestEigenvalue, op!{$op}, $x⟩]])

  -- Integral invariants
  | `(hog{chromaticIndex $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.ChromaticIndex, op!{$op}, $n⟩]])
  | `(hog{chromaticNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.ChromaticNumber, op!{$op}, $n⟩]])
  | `(hog{circumference $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Circumference, op!{$op}, $n⟩]])
  | `(hog{cliqueNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.CliqueNumber, op!{$op}, $n⟩]])
  | `(hog{degeneracy $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Degeneracy, op!{$op}, $n⟩]])
  | `(hog{density $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Density, op!{$op}, $n⟩]])
  | `(hog{diameter $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Diameter, op!{$op}, $n⟩]])
  | `(hog{dominationNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.DominationNumber, op!{$op}, $n⟩]])
  | `(hog{edgeConnectivity $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.EdgeConnectivity, op!{$op}, $n⟩]])
  | `(hog{feedbackVertexSetNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.FeedbackVertexSetNumber, op!{$op}, $n⟩]])
  | `(hog{genus $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Genus, op!{$op}, $n⟩]])
  | `(hog{girth $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Girth, op!{$op}, $n⟩]])
  | `(hog{groupSize $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.GroupSize, op!{$op}, $n⟩]])
  | `(hog{independenceNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.IndependenceNumber, op!{$op}, $n⟩]])
  | `(hog{lengthOfLongestInducedCycle $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.LengthOfLongestInducedCycle, op!{$op}, $n⟩]])
  | `(hog{lengthOfLongestInducedPath $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.LengthOfLongestInducedPath, op!{$op}, $n⟩]])
  | `(hog{lengthOfLongestPath $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.LengthOfLongestPath, op!{$op}, $n⟩]])
  | `(hog{matchingNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.MatchingNumber, op!{$op}, $n⟩]])
  | `(hog{maximumDegree $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.MaximumDegree, op!{$op}, $n⟩]])
  | `(hog{minimumDegree $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.MinimumDegree, op!{$op}, $n⟩]])
  | `(hog{numberOfComponents $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfComponents, op!{$op}, $n⟩]])
  | `(hog{numberOfEdges $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfEdges, op!{$op}, $n⟩]])
  | `(hog{numberOfSpanningTrees $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfSpanningTrees, op!{$op}, $n⟩]])
  | `(hog{numberOfTriangles $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfTriangles, op!{$op}, $n⟩]])
  | `(hog{numberOfVertexOrbits $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfVertexOrbits, op!{$op}, $n⟩]])
  | `(hog{numberOfVertices $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfVertices, op!{$op}, $n⟩]])
  | `(hog{numberOfZeroEigenvalues $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.NumberOfZeroEigenvalues, op!{$op}, $n⟩]])
  | `(hog{radius $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Radius, op!{$op}, $n⟩]])
  | `(hog{treewidth $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.Treewidth, op!{$op}, $n⟩]])
  | `(hog{vertexConnectivity $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.VertexConnectivity, op!{$op}, $n⟩]])
  | `(hog{vertexCoverNumber $op $n}) => `([[HoGEnquiry.IntegralEnquiry ⟨.VertexCoverNumber, op!{$op}, $n⟩]])

  | `(hog{( $q )}) =>
    `(hog{$q})

  | `(hog{$q₁ ∧ $q₂}) =>
    `(distribute hog{$q₁} hog{$q₂})

  | `(hog{$q₁ ∨ $q₂}) =>
    `(List.append hog{$q₁} hog{$q₂})

  | _ => Macro.throwUnsupported

structure DivWithLink where
  text : String
  link : String
  linkText : String

open ProofWidgets in
def DivWithLink.toHtml (dl : DivWithLink) : ProofWidgets.Html :=
  .element "div"
    #[]
    #[
      .text dl.text,
      .element "a"
        #[("href", dl.link)]
        #[(.text dl.linkText)]
    ]

open ProofWidgets in
def putInDiv : List DivWithLink → Html := fun hs =>
  .element "div" #[] (hs.toArray.map DivWithLink.toHtml)

syntax (name := searchForExample) "#search_hog " term : command

open ProofWidgets in
@[command_elab searchForExample]
unsafe def searchForExampleImpl : CommandElab
  | stx@`(#search_hog $q ) => do
    let qs ← liftTermElabM do
      let qe : Expr ← elabTerm q none
      let query ← mkAppM ``Queries.mk #[(← mkAppM ``List.map #[(← mkAppM ``HoGQuery.build #[]), qe])]
      let qs : Queries ← evalExpr' Queries ``Queries query
      return qs

    let queryHash := qs.hash
    let opts ← getOptions
    let py := opts.get hog.pythonExecutable.name hog.pythonExecutable.defValue
    for q in qs.queries do
      let exitCode ← IO.Process.spawn {
        cmd := py
        args := #["Convert/searchHoG.py", s!"{q.query}", s!"{queryHash}"]
      } >>= (·.wait)
      if exitCode ≠ 0 then
        IO.eprintln s!"failed to download graph"
        return

    let path : System.FilePath := System.mkFilePath ["build", s!"search_results_{queryHash}"]
    let contents ← path.readDir
    let resultsList := contents.toList
    let mut i := 1
    let mut ids := []
    let mut graphId := ""
    let mut links := []
    for result in resultsList do
      let path := result.path
      let jsonData ← loadJSONData path
      match jsonData.hogId with
      | none =>
        graphId := s!"result_{i}"
        i := i + 1
        let graphWLink : DivWithLink := ⟨s!"Found solution {graphId}", "", ""⟩
        links := graphWLink :: links
      | some id =>
        graphId := s!"hog_{id}"
        ids := id :: ids
        let houseofgraphsLink := s!"https://houseofgraphs.org/graphs/{id}"
        let graphWLink : DivWithLink := ⟨"Found solution ", houseofgraphsLink, graphId⟩
        links := graphWLink :: links
      let graphName := mkIdent (Name.mkSimple graphId)
      loadGraphAux graphName.getId jsonData false

    let text : DivWithLink := ⟨s!"Found {resultsList.length} graphs satisfying given query", "", ""⟩
    links := text :: links
    Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode (putInDiv links)) }) stx

  | _ => throwUnsupportedSyntax

-- #search_hog hog{ bipartite = true ∧ (numberOfEdges = 1 ∨ numberOfVertices < 6) }
