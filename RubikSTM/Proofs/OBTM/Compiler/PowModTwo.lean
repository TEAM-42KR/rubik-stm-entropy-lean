import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_pow_mod_two {G : Type*} [Group G] (Q : G) (hQ : Q^2=1) (m : ℕ) :
  Q^m = Q^(m%2) := by
  exact pow_eq_pow_of_modEq (by simp [Nat.ModEq]) hQ

#print axioms proof_RubikOBTMCompiler_pow_mod_two
