
import LeanHoG.Graph

namespace LeanHoG

def isIndependentVertexSet {G : Graph} (S : Finset G.vertex) : Prop :=
  ∀ (u v : G.vertex), u ∈ S ∧ v ∈ S → ¬ G.adjacent u v

def isMaximumIndependentVertexSet {G : Graph} (S : Finset G.vertex)
  (_ : isIndependentVertexSet S) : Prop :=
  ∀ (S' : Finset G.vertex), isIndependentVertexSet S' → S'.card ≤ S.card


end LeanHoG
