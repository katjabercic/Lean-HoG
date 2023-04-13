import Graph

class EdgeSize (G : Graph) : Type :=
  edgeSize : ℕ
  correct : edgeSize == G.edgeMap
