import Mathlib
set_option autoImplicit false

theorem proof_RubikGeometry_G_sum_powers_le (a d : ℕ) :
    (∑ j ∈ Finset.range (d + 1), a ^ j) ≤ (a + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range (d + 1), a ^ j) + a ^ (d + 1) ≤
            (a + 1) ^ d + a * (a + 1) ^ d := by
          exact Nat.add_le_add ih (by
            rw [pow_succ']
            exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) d))
        _ = (a + 1) ^ (d + 1) := by rw [pow_succ]; ring
