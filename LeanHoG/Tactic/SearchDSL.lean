import Lean
import Qq
import Lean.Data.Json.Basic
import LeanHoG.LoadGraph
import LeanHoG.Widgets
import LeanHoG.Tactic.Options

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

instance : ToString BoolInvariant where
  toString := fun i =>
    match i with
    | .Acyclic => "Acyclic"
    | .Bipartite => "Bipartite"
    | .Connected => "Connected"
    | .ClawFree => "ClawFree"
    | .Eulerian => "Eulerian"
    | .Hamiltonian => "Hamiltonian"
    | .Hypohamiltonian => "Hypohamiltonian"
    | .Hypotraceable => "Hypotraceable"
    | .Planar => "Planar"
    | .Regular => "Regular"
    | .Traceable => "Traceable"
    | .TwinFree => "TwinFree"

inductive NumericalInvariant where
  | AlgebraicConnectivity
  | AverageDegree
  | Index
  | LaplacianLargestEigenvalue
  | SecondLargestEigenvalue
  | SmallestEigenvalue
deriving Repr, Hashable

instance : ToString NumericalInvariant where
  toString := fun i =>
    match i with
    | .AlgebraicConnectivity => "AlgebraicConnectivity"
    | .AverageDegree => "AverageDegree"
    | .Index => "Index"
    | .LaplacianLargestEigenvalue => "LaplacianLargestEigenvalue"
    | .SecondLargestEigenvalue => "SecondLargestEigenvalue"
    | .SmallestEigenvalue => "SmallestEigenvalue"

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

instance : ToString IntegralInvariant where
  toString := fun i =>
    match i with
    | .ChromaticIndex => "ChromaticIndex"
    | .ChromaticNumber => "ChromaticNumber"
    | .Circumference => "Circumference"
    | .CliqueNumber => "CliqueNumber"
    | .Degeneracy => "Degeneracy"
    | .Density => "Density"
    | .Diameter => "Diameter"
    | .DominationNumber => "DominationNumber"
    | .EdgeConnectivity => "EdgeConnectivity"
    | .FeedbackVertexSetNumber => "FeedbackVertexSetNumber"
    | .Genus => "Genus"
    | .Girth => "Girth"
    | .GroupSize => "GroupSize"
    | .IndependenceNumber => "IndependenceNumber"
    | .LengthOfLongestInducedCycle => "LengthOfLongestInducedCycle"
    | .LengthOfLongestInducedPath => "LengthOfLongestInducedPath"
    | .LengthOfLongestPath => "LengthOfLongestPath"
    | .MatchingNumber => "MatchingNumber"
    | .MaximumDegree => "MaximumDegree"
    | .MinimumDegree => "MinimumDegree"
    | .NumberOfComponents => "NumberOfComponents"
    | .NumberOfEdges => "NumberOfEdges"
    | .NumberOfSpanningTrees => "NumberOfSpanningTrees"
    | .NumberOfTriangles => "NumberOfTriangles"
    | .NumberOfVertexOrbits => "NumberOfVertexOrbits"
    | .NumberOfVertices => "NumberOfVertices"
    | .NumberOfZeroEigenvalues => "NumberOfZeroEigenvalues"
    | .Radius => "Radius"
    | .Treewidth => "Treewidth"
    | .VertexConnectivity => "VertexConnectivity"
    | .VertexCoverNumber => "VertexCoverNumber"

inductive Invariant where
  | BoolInvariant : BoolInvariant → Invariant
  | NumericalInvariant : NumericalInvariant → Invariant
  | IntegralInvariant : IntegralInvariant → Invariant
deriving Repr, Hashable

instance : ToString Invariant where
  toString := fun i =>
    match i with
    | .BoolInvariant b => toString b
    | .NumericalInvariant n => toString n
    | .IntegralInvariant i => toString i

def BoolInvariant.toId : BoolInvariant → Nat
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

def NumericalInvariant.toId : NumericalInvariant → Nat
  | .AlgebraicConnectivity => 19
  | .AverageDegree => 2
  | .Index => 21
  | .LaplacianLargestEigenvalue => 22
  | .SecondLargestEigenvalue => 23
  | .SmallestEigenvalue => 24

def IntegralInvariant.toId : IntegralInvariant → Nat
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
  | .BoolInvariant inv => BoolInvariant.toId inv
  | .NumericalInvariant inv => NumericalInvariant.toId inv
  | .IntegralInvariant inv => IntegralInvariant.toId inv

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
  toString := fun cmp =>
    match cmp with
    | .Eq => "EQ"
    | .Ne => "NE"
    | .Lt => "LT"
    | .Le => "LE"
    | .Gt => "GT"
    | .Ge => "GE"

def ComparisonOp.toAPIRepr : ComparisonOp → String
  | .Eq => "="
  | .Ne => "!="
  | .Lt => "<"
  | .Le => "<="
  | .Gt => ">"
  | .Ge => ">="

inductive Arith where
  | plus
  | minus
  | times
  | div
deriving Repr, Hashable

instance : ToString Arith where
  toString := fun a => match a with
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"

inductive ArithExpr where
  | nat : Nat -> ArithExpr
  | float : Float -> ArithExpr
  | integralInv : IntegralInvariant -> ArithExpr
  | numeralInv : NumericalInvariant -> ArithExpr
  | comp : Arith -> ArithExpr -> ArithExpr -> ArithExpr
deriving Repr, Hashable

def ArithExpr.toString : ArithExpr → String
  | .nat n => s!"{n}"
  | .float x => s!"{x}"
  | .integralInv inv => s!"{inv}"
  | .numeralInv inv => s!"{inv}"
  | .comp op lhs rhs => s!"({lhs.toString}){op}({rhs.toString})"

instance : ToString ArithExpr where
  toString := ArithExpr.toString

/-- Used for making API calls to HoG for formulas. -/
def ArithExpr.toAPIRepr : ArithExpr → String
  | .nat n => s!"{n}"
  | .float x => s!"{x}"
  | .integralInv inv => s!"${inv.toId}$"
  | .numeralInv inv => s!"${inv.toId}$"
  | .comp op lhs rhs => s!"{lhs.toAPIRepr}{op}{rhs.toAPIRepr}"

/-- TODO: Maybe this is a big strange -/
instance : ToJson ArithExpr where
  toJson := fun ae => Json.str ae.toAPIRepr

structure BoolEnquiry where
  inv : BoolInvariant
  val : Bool
deriving Repr, Hashable

instance : ToString BoolEnquiry where
  toString := fun b => s!"{b.inv} = {b.val}"

structure NumericalEnquiry where
  inv : NumericalInvariant
  op : ComparisonOp
  val : Float
deriving Repr, Hashable

instance : ToString NumericalEnquiry where
  toString := fun n => s!"{n.inv} {n.op} {n.val}"

structure IntegralEnquiry where
  inv : IntegralInvariant
  op : ComparisonOp
  val : Int
deriving Repr, Hashable

instance : ToString IntegralEnquiry where
  toString := fun i => s!"{i.inv} {i.op} {i.val}"

structure FormulaEnquiry where
  lhs : ArithExpr
  rhs : ArithExpr
  cmp : ComparisonOp
deriving Repr, Hashable

instance : ToString FormulaEnquiry where
  toString := fun f => s!"{f.lhs.toAPIRepr}{f.cmp.toAPIRepr}{f.rhs.toAPIRepr}"

inductive HoGEnquiry where
  | BoolEnquiry : BoolEnquiry → HoGEnquiry
  | NumericalEnquiry : NumericalEnquiry → HoGEnquiry
  | IntegralEnquiry : IntegralEnquiry → HoGEnquiry
  | FormulaEnquiry : FormulaEnquiry → HoGEnquiry
deriving Repr, Hashable

instance : ToString HoGEnquiry where
  toString := fun enq =>
    match enq with
    | .BoolEnquiry b => toString b
    | .NumericalEnquiry n => toString n
    | .IntegralEnquiry i => toString i
    | .FormulaEnquiry f => toString f

structure InvariantQuery where
  invariantId : Nat
  operator : String
  value : Float
deriving Lean.ToJson, Hashable

structure GraphClassQuery where
  invariantId : Nat
  hasClass : Bool
deriving Lean.ToJson, Hashable

structure FormulaQuery where
  strFormula : String
deriving Lean.ToJson, Hashable

structure HoGQuery where
  invariantEnquiries : List InvariantQuery
  invariantRangeEnquiries : List Int := []
  interestingInvariantEnquiries : List Int := []
  graphClassEnquiries : List GraphClassQuery
  invariantParityEnquiries : List Int := []
  textEnquiries : List String := []
  formulaEnquiries : List FormulaQuery
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

abbrev QueryState := List InvariantQuery × List GraphClassQuery × List FormulaQuery

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
    let (invq,gcq,fmlq) ← get
    return { invariantEnquiries := invq, graphClassEnquiries := gcq, formulaEnquiries := fmlq }
  | .BoolEnquiry ⟨.Bipartite, b⟩ :: es => do
    let (invq,gcq,fmlq) ← get
    set (invq, ⟨(Invariant.BoolInvariant .Bipartite).toId, b⟩ :: gcq, fmlq)
    helper es
  | .BoolEnquiry ⟨inv, b⟩ :: es => do
    let (invq,gcq,fmlq) ← get
    set (invq, boolInvariantToQuery inv b :: gcq, fmlq)
    helper es
  | .NumericalEnquiry ⟨inv, op, x⟩ :: es => do
    let (invq,gcq,fmlq) ← get
    set (numericalInvariantToQuery inv op x :: invq, gcq, fmlq)
    helper es
  | .IntegralEnquiry ⟨inv, op, n⟩ :: es => do
    let (invq,gcq,fmlq) ← get
    set (integralInvariantToQuery inv op n :: invq, gcq, fmlq)
    helper es
  | .FormulaEnquiry f :: es => do
    let (invq,gcq,fmlq) ← get
    set (invq, gcq, ⟨s!"{f}"⟩ :: fmlq)
    helper es

  let (j, _) := helper q ([],[],[])
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

declare_syntax_cat comparison
syntax " = " : comparison
syntax " < " : comparison
syntax " != ": comparison
syntax " > " : comparison
syntax " <= " : comparison
syntax " >= " : comparison
syntax "op!{"  comparison "}" : term

macro_rules
  | `(op!{=}) => `(ComparisonOp.Eq)
  | `(op!{<}) => `(ComparisonOp.Lt)
  | `(op!{!=}) => `(ComparisonOp.Ne)
  | `(op!{>}) => `(ComparisonOp.Gt)
  | `(op!{<=}) => `(ComparisonOp.Le)
  | `(op!{>=}) => `(ComparisonOp.Ge)

declare_syntax_cat comparison_formula
declare_syntax_cat arith_op

syntax "+" : arith_op
syntax "-" : arith_op
syntax "*" : arith_op
syntax "/" : arith_op
syntax "arith_op{" arith_op "}" : term

macro_rules
  | `(arith_op{ + }) => `(Arith.plus)
  | `(arith_op{ - }) => `(Arith.minus)
  | `(arith_op{ * }) => `(Arith.times)
  | `(arith_op{ / }) => `(Arith.div)

syntax comparison_invariant : comparison_formula
syntax:50 comparison_formula:51 arith_op comparison_formula:50 : comparison_formula
syntax:52 num arith_op comparison_formula:52 : comparison_formula
syntax:50 comparison_formula:51 arith_op num : comparison_formula
syntax "(" comparison_formula ")" : comparison_formula
syntax "fmla!{" comparison_formula "}" : term

macro_rules
  | `(fmla!{($fmla)}) => `(fmla!{$fmla})
  | `(fmla!{chromaticIndex}) => `(ArithExpr.integralInv .ChromaticIndex)
  | `(fmla!{chromaticNumber}) => `(ArithExpr.integralInv .ChromaticNumber)
  | `(fmla!{circumference}) => `(ArithExpr.integralInv .Circumference)
  | `(fmla!{cliqueNumber}) => `(ArithExpr.integralInv .CliqueNumber)
  | `(fmla!{degeneracy}) => `(ArithExpr.integralInv .Degeneracy)
  | `(fmla!{density}) => `(ArithExpr.integralInv .Density)
  | `(fmla!{diameter}) => `(ArithExpr.integralInv .Diameter)
  | `(fmla!{dominationNumber}) => `(ArithExpr.integralInv .DominationNumber)
  | `(fmla!{edgeConnectivity}) => `(ArithExpr.integralInv .EdgeConnectivity)
  | `(fmla!{feedbackVertexSetNumber}) => `(ArithExpr.integralInv .FeedbackVertexSetNumber)
  | `(fmla!{genus}) => `(ArithExpr.integralInv .Genus)
  | `(fmla!{girth}) => `(ArithExpr.integralInv .Girth)
  | `(fmla!{groupSize}) => `(ArithExpr.integralInv .GroupSize)
  | `(fmla!{independenceNumber}) => `(ArithExpr.integralInv .IndependenceNumber)
  | `(fmla!{lengthOfLongestInducedCycle}) => `(ArithExpr.integralInv .LengthOfLongestInducedCycle)
  | `(fmla!{lengthOfLongestInducedPath}) => `(ArithExpr.integralInv .LengthOfLongestInducedPath)
  | `(fmla!{lengthOfLongestPath}) => `(ArithExpr.integralInv .LengthOfLongestPath)
  | `(fmla!{matchingNumber}) => `(ArithExpr.integralInv .MatchingNumber)
  | `(fmla!{maximumDegree}) => `(ArithExpr.integralInv .MaximumDegree)
  | `(fmla!{minimumDegree}) => `(ArithExpr.integralInv .MinimumDegree)
  | `(fmla!{numberOfComponents}) => `(ArithExpr.integralInv .NumberOfComponents)
  | `(fmla!{numberOfEdges}) => `(ArithExpr.integralInv .NumberOfEdges)
  | `(fmla!{numberOfSpanningTrees}) => `(ArithExpr.integralInv .NumberOfSpanningTrees)
  | `(fmla!{numberOfTriangles}) => `(ArithExpr.integralInv .NumberOfTriangles)
  | `(fmla!{numberOfVertexOrbits}) => `(ArithExpr.integralInv .NumberOfVertexOrbits)
  | `(fmla!{numberOfVertices}) => `(ArithExpr.integralInv .NumberOfVertices)
  | `(fmla!{numberOfZeroEigenvalues}) => `(ArithExpr.integralInv .NumberOfZeroEigenvalues)
  | `(fmla!{radius}) => `(ArithExpr.integralInv .Radius)
  | `(fmla!{treewidth}) => `(ArithExpr.integralInv .Treewidth)
  | `(fmla!{vertexConnectivity}) => `(ArithExpr.integralInv .VertexConnectivity)
  | `(fmla!{vertexCoverNumber}) => `(ArithExpr.integralInv .VertexCoverNumber)
  | `(fmla!{algebraicConnectivity}) => `(ArithExpr.numericalInv .AlgebraicConnectivity)
  | `(fmla!{averageDegree}) => `(ArithExpr.numericalInv .AverageDegree)
  | `(fmla!{index}) => `(ArithExpr.numericalInv .Index)
  | `(fmla!{laplacianLargestEigenvalue}) => `(ArithExpr.numericalInv .LaplacianLargestEigenvalue)
  | `(fmla!{secondLargestEigenvalue}) => `(ArithExpr.numericalInv .SecondLargestEigenvalue)
  | `(fmla!{smallestEigenvalue}) => `(ArithExpr.numericalInv .SmallestEigenvalue)

  | `(fmla!{$n:num $op:arith_op $fmla:comparison_formula}) => `(ArithExpr.comp arith_op{$op} (ArithExpr.nat $n) fmla!{$fmla})
  | `(fmla!{$f₁:comparison_formula $op:arith_op $f₂:comparison_formula}) => `(ArithExpr.comp arith_op{$op} fmla!{$f₁} fmla!{$f₂})
  | `(fmla!{$fmla:comparison_formula $op:arith_op $n:num}) => `(ArithExpr.comp arith_op{$op} fmla!{$fmla} (ArithExpr.nat $n))

declare_syntax_cat hog_query
syntax (name := hog) "hog{ " hog_query " }" : term
syntax:40 boolean_invariant:41 " = " term:40 : hog_query
syntax:40 comparison_invariant:41 comparison term:40 : hog_query

syntax:41 comparison_formula:42 comparison comparison_formula:41 : hog_query

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

  | `(hog{$fmla1:comparison_formula $cmp:comparison $fmla2:comparison_formula}) => do
    `([[HoGEnquiry.FormulaEnquiry ⟨fmla!{$fmla1}, fmla!{$fmla2}, op!{$cmp}⟩]])

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

structure QueryResult where
  graphId : Ident

unsafe def queryDatabaseForExamples (queries : List ConstructedQuery) (queryHash : UInt64) :
  CommandElabM (List QueryResult) := do
  let opts ← getOptions
  let pythonExe := opts.get leanHoG.pythonExecutable.name leanHoG.pythonExecutable.defValue
  for q in queries do
    let output ← IO.Process.output {
      cmd := pythonExe
      args := #["Convert/searchHoG.py", s!"{q.query}", s!"{queryHash}"]
    }
    if output.exitCode ≠ 0 then
      throwError f!"failed to download graphs: {output.stderr}"

  let path : System.FilePath := System.mkFilePath ["build", "search_results", s!"{queryHash}"]
  let contents ← path.readDir
  let resultsList := contents.toList
  let mut graphId := ""
  let mut results := []
  for result in resultsList do
    let path := result.path
    let jsonData ← loadJSONData path
    match jsonData.hogId with
    | none => throwError m!"Result did not have HoG ID"
    | some id => graphId := s!"hog_{id}"
      let graphName := mkIdent (Name.mkSimple graphId)
      let _ ← loadGraphAux graphName.getId jsonData false
      results := ⟨graphName⟩ :: results
  return results

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

    let opts ← getOptions
    let pythonExe := opts.get leanHoG.pythonExecutable.name leanHoG.pythonExecutable.defValue
    for q in qs.queries do
      IO.println s!"{q.query}"
      let output ← IO.Process.output {
        cmd := pythonExe
        args := #["Convert/searchHoG.py", s!"{q.query}", s!"{qs.hash}"]
      }
      if output.exitCode ≠ 0 then
        IO.println output.stdout
        IO.eprintln f!"failed to download graphs: {output.stderr}"
        return
    -- IO.println s!"{qs.hash}"

    let path : System.FilePath := System.mkFilePath ["build", "search_results", s!"{qs.hash}"]
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
      let _ ← loadGraphAux graphName.getId jsonData false

    let text : DivWithLink := ⟨s!"Found {links.length} graphs satisfying given query", "", ""⟩
    links := text :: links
    Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.RpcEncodable.rpcEncode (putInDiv links)) }) stx

  | _ => throwUnsupportedSyntax
