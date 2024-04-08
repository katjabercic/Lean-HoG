import LeanHoG.Graph
import LeanHoG.Invariant.ConnectedComponents.Basic
import Mathlib.Order.Basic
import Std.Data.RBMap.Lemmas
import Mathlib.Init.Order.Defs

namespace LeanHoG

class IndependentSet extends Graph where
  edgeSet := Std.RBSet.empty
  noEdge : edgeSet = ∅

lemma not_adjacent (I : IndependentSet) (u v : I.vertex) : ¬ I.adjacent u v := by
  unfold Graph.adjacent
  unfold Graph.badjacent
  unfold ltByCases
  intro hyp
  apply ltByCases u v
  · intro cmp
    simp [cmp] at hyp
    rw [I.noEdge] at hyp
    contradiction
  · intro cmp
    simp [cmp] at hyp
  · intro cmp
    have other_cmp : ¬ u < v := by
      simp
      exact le_of_lt cmp
    simp [other_cmp, cmp] at hyp
    rw [I.noEdge] at hyp
    contradiction

instance : Coe IndependentSet Graph := by
  sorry

lemma not_connected (G : Graph) (u v : G.vertex) : G.edgeSet = ∅ → G.connected u v → u = v := by
  sorry

instance (I : IndependentSet) : ConnectedComponents I :=
  let G : Graph := I
  let component := fun x => x
  have inhabited : ∀ (i : Fin G.vertexSize), ∃ u, component u = i := by
    intro i
    use i
  have correct : ∀ (u v : G.vertex), component u = component v ↔ G.connected u v := by
    intro u v
    simp
    constructor
    · intro eq
      apply Graph.connected_of_eq
      assumption
    · intro connected
      apply not_connected G u v I.noEdge connected
  {
    val := G.vertexSize
    component := component
    componentInhabited := inhabited
    correct := correct
  }

end LeanHoG
