import .tactic
import data.fintype.basic
namespace hypermap
structure hypermap : Type :=
  (dart_size: ℕ)
  (edge: (fin dart_size) → (fin dart_size))
  (node: (fin dart_size) → (fin dart_size)) 
  (face: (fin dart_size) → (fin dart_size))
  (cancel3: function.right_inverse (λ dart, node (face dart)) edge . bool_reflect)
variable (h : hypermap)

lemma edge_inv : function.right_inverse (λ dart, h.node (h.face dart)) h.edge :=
  h.cancel3
lemma edge_surjective : function.surjective h.edge :=
  function.right_inverse.surjective h.cancel3
lemma edge_injective : function.injective h.edge :=
begin
  rw fintype.injective_iff_surjective,
  exact edge_surjective h
end

lemma face_inv : function.right_inverse h.face (λ dart, h.edge (h.node dart)) :=
  edge_inv h
lemma face_injective : function.injective h.face :=
begin
  apply function.left_inverse.injective,
  apply face_inv
end
lemma face_surjective : function.surjective h.face :=
begin
  rw ←fintype.injective_iff_surjective,
  exact face_injective h
end

lemma node_inv : function.left_inverse (λ dart, h.face (h.edge dart)) h.node :=
begin
  have h1 : function.left_inverse h.face (λ dart, h.edge (h.node dart)), from 
    function.left_inverse_of_surjective_of_right_inverse (face_surjective h) (edge_inv h),
  show function.left_inverse (λ dart, h.face (h.edge dart)) h.node, from h1
end
lemma node_injective : function.injective h.node :=
begin
  apply function.left_inverse.injective,
  exact node_inv h
end
lemma node_surjective : function.surjective h.node :=
begin
  rw ←fintype.injective_iff_surjective, 
  exact node_injective h
end
 
end hypermap

