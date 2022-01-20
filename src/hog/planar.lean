import .tactic
import .perm_cycles
import data.fintype.basic
import group_theory.group_action.basic
import group_theory.perm.cycles
namespace hypermap
structure hypermap : Type :=
  (dart_size: ℕ)
  (edge: (fin dart_size) → (fin dart_size))
  (node: (fin dart_size) → (fin dart_size)) 
  (face: (fin dart_size) → (fin dart_size))
  (cancel3: 
    function.right_inverse 
      (λ dart, node (face dart)) 
      edge 
  . bool_reflect)
variable (h : hypermap)

lemma edge_inv : 
function.right_inverse 
  (λ dart, h.node (h.face dart)) 
  h.edge 
:= h.cancel3

lemma edge_surjective : function.surjective h.edge :=
  function.right_inverse.surjective h.cancel3

lemma edge_injective : function.injective h.edge :=
begin
  rw fintype.injective_iff_surjective,
  exact edge_surjective h
end

lemma face_inv : 
function.right_inverse 
  h.face 
  (λ dart, h.edge (h.node dart)) 
:= edge_inv h

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

lemma node_inv : 
function.left_inverse 
  (λ dart, h.face (h.edge dart)) 
  h.node 
:=
begin
  have h1 : function.left_inverse h.face (λ dart, h.edge (h.node dart)), 
  from 
    function.left_inverse_of_surjective_of_right_inverse 
      (face_surjective h) 
      (edge_inv h),
  show function.left_inverse (λ dart, h.face (h.edge dart)) h.node, 
  from h1
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

def edge_perm : equiv.perm (fin h.dart_size) := 
{ equiv.
  to_fun := h.edge,
  inv_fun := (λ dart, h.node (h.face dart)),
  left_inv := 
    function.left_inverse_of_surjective_of_right_inverse 
      (function.surjective.comp 
        (node_surjective h) 
        (face_surjective h)
      )
      (edge_inv h),
  right_inv := edge_inv h 
}

def node_perm : equiv.perm (fin h.dart_size) := 
{ equiv.
  to_fun := h.node,
  inv_fun := (λ dart, h.face (h.edge dart)),
  left_inv := node_inv h,
  right_inv := 
    function.right_inverse_of_injective_of_left_inverse 
      (function.injective.comp (face_injective h) (edge_injective h))
      (node_inv h) 
}

def face_perm : equiv.perm (fin h.dart_size) := 
{ equiv.
  to_fun := h.face,
  inv_fun := (λ dart, h.edge (h.node dart)),
  left_inv := face_inv h,
  right_inv := 
    function.right_inverse_of_injective_of_left_inverse 
      (function.injective.comp (edge_injective h) (node_injective h))
      (face_inv h) 
}

end hypermap

namespace euler_characteristic
open hypermap
def count_cycles {n : ℕ} {f : fin n → fin n} (l : cycles_of f)  : ℕ :=
list.length l.val

structure euler_char (h : hypermap) (n : ℤ): Type :=
  (edge_cycles : cycles_of h.edge . gen_factorization)
  (node_cycles : cycles_of h.node . gen_factorization)
  (face_cycles : cycles_of h.face . gen_factorization)
  (char_is_n : 
    n = 
    node_cycles.val.length - 
    edge_cycles.val.length + 
    face_cycles.val.length 
  . bool_reflect)

end euler_characteristic

