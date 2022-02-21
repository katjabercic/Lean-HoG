import .graph
import .component

variable g : simple_irreflexive_graph

-- inductive definition of path in a graph
-- a path is either just an edge or it is constructed from a path and a next edge that fits
inductive path (last : edge g) : Type
| trivial : path
| cons (next : edge g) (p : path) : next.i = last.j → path

notation p ,, next  := path.cons next p
-- notation `[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := l

@[reducible, simp]
def path_start (last : edge g) : path g last → edge g
| path.trivial := last
| (path.cons next p cond) := path_start p

def path_concat (last₁ last₂ : edge g) (p : path g last₁) : path g last₂ → path g last₂
| path.trivial := path.cons last₂ p _
| (path.cons next p cond) := _



def symm_path (last : edge g) (p : path g last) : path g (path_start g last p) :=
match p with
| path.trivial := p
| (path.cons next p cond) := path.cons (path_start g last p)
end

-- def path_is_path {g : simple_irreflexive_graph} : list (edge g) → Prop
-- | [] := false
-- | (e :: es) :=
--   match list.nth es 1 with
--   | option.none := true
--   | option.some e' := e.j = e'.i ∧ path_is_path es
--   end

-- trying to get a nice path definition
-- structure path (g : simple_irreflexive_graph) : Type :=
--   (s t : fin g.vertex_size)
--   (edges : list (edge g))
--   [nonempty : inhabited (edge g)]
--   (is_path : path_is_path edges)
--   (correct_ends : edges.head.i = s ∧ edges.ilast.j = t)

-- very very ugly definition of a path between two vertices
-- structure path (g : simple_irreflexive_graph) : Type :=
--   (i j : fin g.vertex_size)
--   (path_len : ℕ)
--   (pos_length : 0 < path_len)
--   [non_zero : has_zero (fin path_len)]
--   (path : fin path_len → (fin g.vertex_size × fin g.vertex_size))
--   (path_is_edges : ∀ i : fin path_len, g.edge (path i).fst (path i).snd)
--   (is_path : Π (i < path_len-1), (path (fin.mk i (nat.lt_of_lt_pred H))).snd = (path (fin.mk (i+1) (nat.add_lt_of_lt_sub_right H))).fst)
--   (correct_ends : (path 0).fst = i ∧ (path (fin.mk (path_len-1) (buffer.lt_aux_2 pos_length))).snd = j)


-- def symm_path {g : simple_irreflexive_graph} (p : path g) : path g :=
-- { i := p.j,
--   j := p.i,
--   path_len := p.path_len,
--   pos_length := p.pos_length,
--   non_zero := p.non_zero,
--   path := λ i, let e := p.path ((fin.mk (p.path_len-1) (buffer.lt_aux_2 p.pos_length)) - i) in ⟨e.snd, e.fst⟩,
--   path_is_edges := λ v, g.symmetric _ _ (p.path_is_edges ((fin.mk (p.path_len-1) (buffer.lt_aux_2 p.pos_length)) - v)),
--   is_path :=
--     let path : fin p.path_len → (fin g.vertex_size × fin g.vertex_size) := (λ i, let e := p.path ((fin.mk (p.path_len-1) (buffer.lt_aux_2 p.pos_length)) - i) in ⟨e.snd, e.fst⟩) in
--     begin
--       intros i H,
--       simp,
--       let k := ((fin.mk (p.path_len-1) (buffer.lt_aux_2 p.pos_length)) - ⟨i, nat.lt_of_lt_pred H⟩),
--       have H' : (p.path (⟨p.path_len - 1, _⟩ - ⟨i, _⟩)).fst = (p.path (⟨p.path_len - 1, _⟩ - ⟨i + 1, _⟩)).snd :=
--         begin
--           symmetry,
--           apply p.is_path,

--         end 
--     end,
--   correct_ends := _ }