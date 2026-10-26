import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_padCount (r : ℕ) :
  (5 - r % 4) % 4 ≤ 3 ∧ (r + (5 - r % 4) % 4) % 4 = 1 := by
  omega

#print axioms proof_RubikCompiler_padCount
