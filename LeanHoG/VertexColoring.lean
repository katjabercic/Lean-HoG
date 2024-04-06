import LeanHoG.Graph
import LeanHoG.Walk

namespace LeanHoG

@[reducible]
def isVertexColoring {Color : Type} (G : Graph) (c : G.vertex → Color) :=
  ∀ {u v : G.vertex}, G.adjacent u v → c u ≠ c v

structure VertexColoring (Color : Type) [DecidableEq Color] (G : Graph) : Type where
  color : G.vertex → Color
  isColoring :  isVertexColoring G color
deriving Fintype

def VertexColoring.mk' {Color : Type} [DecidableEq Color] (G : Graph) (color : G.vertex → Color) (p : ∀ e : G.edge, color (G.fst e) ≠ color (G.snd e)) :
  VertexColoring Color G := by
  apply VertexColoring.mk color
  apply G.all_adjacent_of_edges (fun u v => color u ≠ color v)
  · intros u v h e ; apply h ; symm ; assumption
  · assumption

@[reducible]
structure TwoColoring (G : Graph) extends VertexColoring (Fin 2) G
deriving Fintype

theorem TwoColoring.even_odd_walk
  {G : Graph}
  {s t : G.vertex}
  (w : Walk G s t)
  (c : TwoColoring G) :
  (Odd w.length → c.color s ≠ c.color t) ∧
  (Even w.length → c.color s = c.color t)
  := by
  induction w with
  | here _ => simp
  | @step s t u e w ih =>
    cases Nat.even_or_odd (Walk.length w) with
    | inl evenw =>
      have _ := c.isColoring e
      simp_all [Walk.length, Nat.even_add_one, evenw]
    | inr oddw =>
      have _ := c.isColoring e
      have _ := ih.1 oddw
      simp_all [Walk.length, Nat.even_add_one]
      have fin2 : ∀ (a b c : Fin 2), a ≠ b → b ≠ c → a = c := by simp [Fin.forall_fin_two]
      apply (fin2 (c.color s) (c.color t) (c.color u)) <;> assumption

theorem TwoColoring.odd_walk {G : Graph} {s t : G.vertex} (c : TwoColoring G) (w : Walk G s t):
  Odd w.length → c.color s ≠ c.color t := (c.even_odd_walk w).left

theorem TwoColoring.even_walk {G : Graph} {s t : G.vertex} (c : TwoColoring G) (w : Walk G s t):
  Even w.length → c.color s = c.color t := (c.even_odd_walk w).right

end LeanHoG
