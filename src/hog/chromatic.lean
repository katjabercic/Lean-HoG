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

lemma chromatic_number_is_unique (g:simple_irreflexive_graph) :
  ∀ c d, is_chromatic_number g c ∧ is_chromatic_number g d → c=d:=
begin
  intros c d chr,
  cases chr with chr_c chr_d,
  dunfold is_chromatic_number at *,
  cases chr_c with chr_c_col chr_c_valid,
  cases chr_d with chr_d_col chr_d_valid,
  specialize chr_c_valid d,
  specialize chr_d_valid c,
  have cd := chr_d_valid chr_c_col,
  have dc := chr_c_valid chr_d_col,
  exact le_antisymm (chr_c_valid chr_d_col) (chr_d_valid chr_c_col),
end


