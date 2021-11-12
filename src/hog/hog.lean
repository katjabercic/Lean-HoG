import combinatorics.simple_graph.basic

namespace hog

open tactic
open tactic.interactive
open interactive (parse)
open interactive.types (texpr)
open lean.parser (ident tk)

def preadjacency := ℕ → ℕ → bool

structure hog : Type :=
 (number_of_vertices : ℕ)
 (graph : simple_graph (fin number_of_vertices))
 (number_of_vertices_eq_size : number_of_vertices = number_of_vertices)
 (acyclic : option bool)
 (bipartite : option bool)
 (chromatic_index : option nat)
 (chromatic_number : option nat)
 (circumference : option nat)
 (claw_free : option bool)
 (clique_number : option nat)
 (connected : option bool)
 (diameter : option nat)
 (edge_connectivity : option nat)
 (eulerian : option bool)
 (genus : option nat)
 (girth : option nat)
 (hamiltonian : option bool)
 (independence_number : option nat)
 (longest_induced_cycle : option nat)
 (longest_induced_path : option nat)
 (matching_number : option nat)
 (maximum_degree : option nat)
 (minimum_degree : option nat)
 (minimum_dominating_set : option nat)
 (number_of_components : option nat)
 (number_of_edges : option nat)
 (number_of_triangles : option nat)
 (planar : option bool)
 (radius : option nat)
 (regular : option bool)
 (vertex_connectivity : option nat)
 
 

@[reducible]
def restrict {α : Type} (f : ℕ → ℕ → α) (n : ℕ) : fin n → fin n → α :=
λ i j, f i.val j.val

@[reducible]
def reducible_to_bool (p : Prop) [h : decidable p] : bool :=
decidable.cases_on h (λ h₁, bool.ff) (λ h₂, bool.tt)

@[reducible]
def boolean_reflection {p : Prop} [d : decidable p] : reducible_to_bool p = true → p := 
begin
  casesI d,
  { simp [reducible_to_bool] },
  { simp, exact d }
end

meta def tactic.interactive.from_preadj (n : parse texpr) (_ : parse $ tk "with") (adj : parse texpr) : tactic unit :=
do { r ← i_to_expr_strict
                  ``(simple_graph.mk
                      (restrict (%%adj) %%n)
                      (begin unfold symmetric, exact boolean_reflection rfl end)
                      (begin unfold irreflexive, exact boolean_reflection rfl end) : simple_graph (fin %%n)
                  ),
     exact r
}

-----------------------------------
-- Example
-----------------------------------

def petersen_preadj : ℕ → ℕ → Prop
-- outer cycle
| 0 1 := true
| 1 2 := true 
| 2 3 := true 
| 3 4 := true 
| 4 0 := true 
| 0 5 := true 
| 1 6 := true 
| 2 7 := true 
| 3 8 := true 
| 4 9 := true 
| 5 7 := true 
| 6 8 := true 
| 7 9 := true 
| 8 5 := true 
| 9 6 := true 
| _ _ := false -- catch all case


def petersen_graph : simple_graph (fin 10) := 
{ simple_graph .
  adj := restrict petersen_preadj 10,
  sym := begin unfold symmetric, from_preadj 10 with petersen_preadj end,
  loopless := begin unfold irreflexive, from_preadj 10 with petersen_preadj end
}

def petersen_hog :=
  { hog . number_of_vertices := 10,
    graph := by from_preadj 10 with petersen_preadj,
    number_of_vertices_eq_size := rfl,
    acyclic := option.none,
    bipartite := option.none,
    chromatic_index := option.none,
    chromatic_number := option.none,
    circumference := option.none,
    claw_free := option.none,
    clique_number := option.none,
    connected := option.none,
    diameter := option.none,
    edge_connectivity := option.none,
    eulerian := option.none,
    genus := option.none,
    girth := option.none,
    hamiltonian := option.none,
    independence_number := option.none,
    longest_induced_cycle := option.none,
    longest_induced_path := option.none,
    matching_number := option.none,
    maximum_degree := option.none,
    minimum_degree := option.none,
    minimum_dominating_set := option.none,
    number_of_components := option.none,
    number_of_edges := option.none,
    number_of_triangles := option.none,
    planar := option.none,
    radius := option.none,
    regular := option.none,
    vertex_connectivity := option.none,
  }

end hog