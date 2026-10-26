import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_powModFour {G : Type*} [Group G] (B : G) (hB : B ^ 4 = 1) (m : ℕ) :
  B ^ m = B ^ (m % 4) := by
  exact pow_eq_pow_of_modEq (by simp [Nat.ModEq]) hB

#print axioms proof_RubikCompiler_powModFour
