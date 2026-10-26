import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_lower_half_coalesces {G : Type*} [Group G] (D : G) (hD : D^4=1) (m : ℕ) :
  (D^2)⁻¹ ^ m = D ^ (2*(m%2)) := by
  have h2 : (D^2)^2=1 := by simpa only [← pow_mul] using hD
  have hinv : (D^2)⁻¹ = D^2 := by
    have H : D^2 * D^2=1 := by simpa only [pow_two] using h2
    calc
      (D^2)⁻¹ = (D^2)⁻¹ * (D^2 * D^2) := by rw [H,mul_one]
      _ = D^2 := by simp [← mul_assoc]
  rw [hinv]
  have H : (D^2)^m = (D^2)^(m%2) :=
    pow_eq_pow_of_modEq (by simp [Nat.ModEq]) h2
  rw [H,← pow_mul]

#print axioms proof_RubikOBTMCompiler_lower_half_coalesces
