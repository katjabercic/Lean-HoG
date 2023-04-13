import Graph

lemma Graph.edgeTreeSize_is_edgeSize (G : Graph) :
  G.edgeSize = G.edgeTree.size := sorry

class EdgeSize (G : Graph) : Type :=
  val : ℕ
  correct : G.edgeTree.size = val := by rfl

-- improve naming
lemma Graph.edgeSize_is (G : Graph) [es : EdgeSize G] : G.edgeSize = es.val := by
  apply Eq.trans (b := G.edgeTree.size)
  · apply edgeTreeSize_is_edgeSize
  · apply es.correct
