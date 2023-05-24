import TreeSet
import Graph

namespace HoG

class NeighborhoodMap (G : Graph) : Type where
  val : G.vertex → STree G.vertex
  correct : ∀ (u v : G.vertex), G.adjacent u v ↔ (val u).mem v

instance (G : Graph) : CoeFun (NeighborhoodMap G) (fun _ => G.vertex → STree G.vertex) where
  coe := @NeighborhoodMap.val G

lemma NeighborhoodMap.neighborhoodSize (G : Graph) [nbh : NeighborhoodMap G] (v : G.vertex) :
  G.degree v = (nbh v).size := by
  apply Eq.trans (b := Fintype.card (nbh v).set)
  · apply Fintype.card_congr
    apply (Equiv.subtypeEquiv (Equiv.refl G.vertex))
    intro u
    exact (nbh.correct v u)
  · apply STree.size_is_card

-- specialized constructor for JSON decoding
def NeighborhoodMap.mk'
  (G : Graph)
  (m : G.vertex → STree G.vertex)
  (H₁ : G.edgeTree.all (fun e => (m (G.fst e)).mem (G.snd e) ∧ (m (G.snd e)).mem (G.fst e)) = true)
  (H₂ : decide (∀ u, (m u).all (fun v => G.badjacent u v)) = true) :
  NeighborhoodMap G :=
  { val := m,
    correct := by
      intros u v
      apply Iff.intro
      · intro uv
        cases G.adjacentAll (fun u v => (m u).mem v ∧ (m v).mem u) H₁ u v uv with
        | inl vmu => exact vmu.1
        | inr vmu => exact vmu.2
      · intro vmu
        exact (m u).all_forall _ (of_decide_eq_true H₂ u) v vmu
  }

end HoG