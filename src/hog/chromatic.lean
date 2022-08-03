-- Define chromatic number
import .graph


structure coloring: Type :=
  (g : simple_irreflexive_graph)
  (ncolors : ℕ)
  (color : fin g.vertex_size → fin ncolors)
  [valid : ∀ i j, g.edge i j → color i ≠ color j]

def coloring_from_edge_list (g:simple_irreflexive_graph) : coloring :=
{ g:=g,
  ncolors := g.vertex_size,
  color := λ i, i,
  valid := begin
    intros i j gij,
    have q:= g.irreflexive i,
    by_contradiction,
    simp at h,
    rw ←  h at gij,
    exact q gij,
  end
}


