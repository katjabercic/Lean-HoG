import LeanHoG.Graph
import LeanHoG.Invariant.ConnectedComponents.Basic
import LeanHoG.Invariant.Bipartite.Basic
import LeanHoG.Invariant.NeighborhoodMap.Basic
import Mathlib.Order.Basic
import Std.Data.RBMap.Lemmas
import Mathlib.Init.Order.Defs
import Mathlib.Logic.Relation
import Mathlib.Init.Data.Quot

namespace LeanHoG

/--
A graph with n vertices and an empty edge set.
-/
def IndependentSet (n : Nat) : Graph :=
  {
    vertexSize := n
    edgeSet := Std.RBSet.empty
  }

/--
  If the edge set is empty then two vertices cannot be adjacent.
-/
-- I know this looks complex for such a trivial case but it should deal with both abstraction from definitions and the imposed ordering on the edges.
lemma empty_edges_impl_not_adj (G : Graph) (u v : G.vertex) : G.edgeSet = Std.RBSet.empty → ¬ G.adjacent u v := by
  intro empty
  unfold Graph.adjacent
  unfold Graph.badjacent
  unfold ltByCases
  intro adjacent
  apply ltByCases u v
  · intro comp
    simp [comp] at adjacent
    rw [empty] at adjacent
    contradiction
  · intro comp
    simp [comp] at adjacent
  · intro comp
    have not_u_lt_v := not_lt_of_gt comp
    simp [comp, not_u_lt_v] at adjacent
    rw [empty] at adjacent
    contradiction

lemma empty_edges_and_diff_impl_not_connected (G : Graph) (u v : G.vertex) : G.edgeSet = Std.RBSet.empty → u ≠ v → ¬ G.connected u v := by
  intro empty ne connected
  unfold Graph.connected at connected
  induction connected with
  | rel x y adj =>
    unfold Graph.adjacent at adj
    unfold Graph.badjacent at adj
    apply ltByCases x y
    · intro x_lt
      simp[x_lt] at adj
      rw [empty] at adj
      contradiction
    · intro eq
      contradiction
    · intro x_gt
      simp[x_gt] at adj
      rw [empty] at adj
      contradiction
  | refl x =>
    contradiction
  | symm x y _ hi =>
    symm at ne
    exact hi ne
  | trans x y z _ _ x_ne_y y_ne_z =>
    cases ne_or_eq x y with
    | inl hi =>
      have _ := x_ne_y hi
      contradiction
    | inr x_eq_y =>
      cases ne_or_eq y z with
      | inl hi =>
        have _ := y_ne_z hi
        contradiction
      | inr hi =>
        have _ := Eq.trans x_eq_y hi
        contradiction

/--
  If the edge set of a graph is empty and two vertices are connected, they can only be equal.
-/
lemma empty_edges_impl_connected_eq (G : Graph) (u v : G.vertex) : G.edgeSet = Std.RBSet.empty → G.connected u v → u = v := by
  intro empty
  apply ltByCases u v
  · intro lt
    -- The adjacent relation should always be false since we have no edges.
    have ne := ne_of_lt lt
    have not_connected := empty_edges_and_diff_impl_not_connected G u v empty ne
    intro connected
    contradiction
  · intro eq _
    assumption
  · intro gt
    -- The adjacent relation should always be false since we have no edges.
    have ne := ne_of_lt gt
    symm at ne
    have not_connected := empty_edges_and_diff_impl_not_connected G u v empty ne
    intro connected
    contradiction

/--
  Instance of ConnectedComponents for the independent set.
-/
instance independentComponents {n : Nat} : ConnectedComponents (IndependentSet n) :=
  let G : Graph := IndependentSet n
  let component := fun x => x
  have inhabited : ∀ (i : Fin G.vertexSize), ∃ (u : G.vertex), component u = i := by
    intro i
    use i
  have correct : ∀ (u v : G.vertex), component u = component v ↔ G.connected u v := by
    intro u v
    simp
    constructor
    · intro eq
      simp [eq]
      apply Graph.connected_of_eq
      rfl
    · intro connected
      have empty : G.edgeSet = Std.RBSet.empty := by rfl
      exact empty_edges_impl_connected_eq G u v empty connected
  {
    val := G.vertexSize
    component := fun x => x
    componentInhabited := inhabited
    correct := correct
  }

/--
  Instance of a BipartiteCertificate for independent sets with at least 2 vertices.
-/
-- Since our definition uses two colorings, a graph with less than two vertices is not bipartite.
def independentBipartite {n : Nat} : 1 < n → BipartiteCertificate (IndependentSet n) := by
  intro gt1
  let G : Graph := IndependentSet n
  let eq_size : G.vertexSize = n := by rfl
  let large_enough : 1 < G.vertexSize := by
    rw [eq_size]; assumption
  let v1 : G.vertex := {val := 0, isLt := by linarith}
  let v2 : G.vertex := {val := 1, isLt := by linarith}
  let color : (IndependentSet n).vertex → Fin 2 := fun x => if x = v1 then 0 else 1
  have col_v1_zero : color v1 = 0 := by simp
  have col_v2_one : color v2 = 1 := by simp
  have is_coloring : ∀ {u v : G.vertex}, G.adjacent u v → color u ≠ color v := by
    intro u v adjacent
    have _ := empty_edges_impl_not_adj G u v (by rfl)
    contradiction
  exact {
    vertex0 := v1
    vertex1 := v2
    color := color
    vertex0Color := col_v1_zero
    vertex1Color := col_v2_one
    isColoring := is_coloring
  }

/--
For testing purposes, this should ideally not be required.
-/
instance certif : BipartiteCertificate (IndependentSet 20) := independentBipartite (by linarith)

#eval (IndependentSet 1).connectedGraph
#eval (IndependentSet 30).connectedGraph

-- Careful, without a certificate, this could take a while and crash lean.
#eval (IndependentSet 20).bipartite

end LeanHoG
