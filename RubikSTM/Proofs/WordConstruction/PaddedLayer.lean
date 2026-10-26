import Mathlib
import RubikSTM.Lemmas.WordConstruction.PowModFour
set_option autoImplicit false

theorem proof_RubikCompiler_paddedLayer {G : Type*} [Group G] (B F : G) (hB : B ^ 4 = 1)
  (t j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t) (ht : t % 4 = 1) :
  B ^ (t-j) * F * B ^ (j-1) =
    (B ^ ((j-1) % 4))⁻¹ * F * B ^ ((j-1) % 4) := by
  have hsum : (t-j) + (j-1) = t-1 := by omega
  have hzero : (t-1) % 4 = 0 := by omega
  have hp : B ^ (t-1) = 1 := by
    rw [RubikCompiler.powModFour B hB (t-1), hzero, pow_zero]
  have hleft : B ^ (t-j) = (B ^ ((j-1) % 4))⁻¹ := by
    calc
      B ^ (t-j) = (B ^ (t-j) * B ^ (j-1)) * (B ^ (j-1))⁻¹ := by
        simp [mul_assoc]
      _ = (B ^ (j-1))⁻¹ := by rw [← pow_add, hsum, hp, one_mul]
      _ = (B ^ ((j-1) % 4))⁻¹ := by rw [RubikCompiler.powModFour B hB (j-1)]
  rw [hleft, RubikCompiler.powModFour B hB (j-1)]

#print axioms proof_RubikCompiler_paddedLayer
