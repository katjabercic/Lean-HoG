import Graph

lemma EdgeSize.edgeTreeSize_is_edgeSize (G : Graph) :
  G.edgeSize = G.edgeTree.size := sorry

class EdgeSize (G : Graph) : Type :=
  val : ℕ
  correct : G.edgeTree.size = edgeSize := by rfl

-- improve naming
lemma EdgeSize.edgeSize_is (G : Graph) [es : EdgeSize G] : G.edgeSize = es.val := by
  apply Eq.trans (b := G.edgeTree.size)
  · apply edgeTreeSize_is_edgeSize
  · apply es.correct
