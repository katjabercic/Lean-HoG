-- Define chromatic number
import .graph

variable G : simple_irreflexive_graph


structure coloring (g : simple_irreflexive_graph) (ncolors : ℕ): Type :=
  (color : fin g.vertex_size → fin ncolors)
  [valid : ∀ i j, g.edge i j → color i ≠ color j]

def coloring_from_edge_list (g:simple_irreflexive_graph) : coloring g g.vertex_size:=
{ color := λ i, i,
  valid := begin
    intros i j gij,
    have q:= g.irreflexive i,
    by_contradiction,
    simp at h,
    rw ←  h at gij,
    exact q gij,
  end
}

def exists_coloring_col (g:simple_irreflexive_graph) (ncolors:ℕ): Prop :=
  nonempty (coloring g ncolors)

lemma exists_coloring (g:simple_irreflexive_graph) :
  ∃ c, nonempty (coloring g c) :=
begin
  use g.vertex_size,
  have q:= coloring_from_edge_list g,
  exact nonempty.intro q,
end

def is_chromatic_number (g:simple_irreflexive_graph) (c:ℕ) :=
  exists_coloring_col g c ∧ (∀ c2, exists_coloring_col g c2 → c2 ≥ c)




