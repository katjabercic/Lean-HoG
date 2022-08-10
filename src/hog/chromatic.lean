-- Define chromatic number
import .graph


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
  ∃ c, exists_coloring_col g c :=
begin
  use g.vertex_size,
  use coloring_from_edge_list g,
end


instance ig (g:simple_irreflexive_graph): decidable_pred (λ (n : ℕ), exists_coloring_col g n) :=
begin
  dunfold exists_coloring_col,
  intros c,
  ring_nf,
  sorry,
end

def chromatic_number (g:simple_irreflexive_graph):nat :=
  nat.find (exists_coloring g)

def testiranje : simple_irreflexive_graph :=
  from_edge_list 1 []


#reduce chromatic_number testiranje

