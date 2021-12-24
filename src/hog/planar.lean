import .tactic

namespace hypermap

structure hypermap : Type :=
  (dart_size: ℕ)
  (edge: (fin dart_size) → (fin dart_size))
  (node: (fin dart_size) → (fin dart_size)) 
  (face: (fin dart_size) → (fin dart_size))
  (cancel3: function.left_inverse edge (λ dart, node (face dart)) . bool_reflect)
end hypermap