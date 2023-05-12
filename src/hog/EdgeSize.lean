import Graph

namespace HoG

lemma Graph.edgeTreeSize_is_edgeSize (G : Graph) :
  G.edgeSize = G.edgeTree.size := sorry

class EdgeSize (G : Graph) : Type :=
  val : ℕ
  correct : G.edgeSize = val

-- smart constructor used to load JSON files
-- def EdgeSize.mk' (G : Graph) (e : Nat) (H : Nat.beq G.edgeTree.size e = true) : EdgeSize G :=
--   ⟨ e , Eq.trans G.edgeTreeSize_is_edgeSize (Nat.eq_of_beq_eq_true H) ⟩

def EdgeSize.mk' (G : Graph) (e : Nat) (H : G.edgeTree.size = e) : EdgeSize G :=
  ⟨ e , Eq.trans G.edgeTreeSize_is_edgeSize H ⟩

end HoG
