import Graph

namespace HoG

lemma Graph.edgeTreeSize_is_edgeSize (G : Graph) :
  G.edgeSize = G.edgeTree.size := sorry

class EdgeSize (G : Graph) : Type :=
  val : ℕ
  correct : G.edgeSize = val

-- smart constructor used to load JSON files
def EdgeSize.mk' (G : Graph) (e : Nat) (H : Nat.beq G.edgeTree.size e = true) : EdgeSize G :=
  ⟨ e , (by apply Eq.trans (b := G.edgeTree.size)
            · apply Graph.edgeTreeSize_is_edgeSize
            · simp_all)⟩

end HoG
