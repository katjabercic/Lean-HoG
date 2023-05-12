import TreeSet
import TreeMap
import Graph

class NeighborMap (G : Graph) : Type :=
  map : Map G.vertex (Tree G.vertex)

  neighbor : G.vertex → G.vertex → Bool :=
    fun u v =>
      match map.get u with
      | none => false
      | some s => s.mem v

  correct : ∀ (u v : G.vertex), G.neighbor u v == neighbor u v
