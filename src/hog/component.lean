-- Graph components

import data.quot
import .graph

@[simp, reducible]
def connected (g : simple_irreflexive_graph) : vertex g → vertex g → Prop :=
  eqv_gen (λ i j, g.edge i j)

-- if we add the edge x-y then x and y are connected
lemma connected_added_edge {g} {x y : vertex g} {ne : x ≠ y} :
  connected (add_edge g x y ne) x y :=
begin
  apply eqv_gen.rel,
  sorry
end


-- connected vertices are still connected when we add an edge
lemma connected_after_add_edge {g} {x y : vertex g} {ne : x ≠ y} (i j : vertex g) :
  connected g i j → connected (add_edge g x y ne) i j :=
sorry

structure decomposition (g : simple_irreflexive_graph) : Type :=
  (anchor : vertex g → vertex g)
  (anchor_is_kernel : ∀ i j, anchor i = anchor j ↔ connected g i j )

lemma decomposition_add_edge {g} (D : decomposition g) (x y : vertex g) (ne : x ≠ y) : decomposition (add_edge g x y ne) :=
  { anchor := (λ i, if D.anchor i = x then D.anchor y else D.anchor x)
  , anchor_is_kernel :=
    begin
      intros i j,
      by_cases aiaj : D.anchor i = D.anchor j,
      { simp [aiaj], have gij := (D.anchor_is_kernel i j).mp aiaj,
         },
      { sorry }
    end  }
