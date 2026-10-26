import Mathlib
set_option autoImplicit false

theorem proof_RubikOBTM_Global_cleanup_scalar_bound (C core m cnt n : ℕ) (hm : m ≤ n) (hn : 1 ≤ n) :
    ((C * (cnt + 6 * m) + 4 * core : ℕ) : ℝ) ≤
      (C : ℝ) * cnt + (6 * (C : ℝ) + 4 * (core : ℝ)) * n := by
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [mul_le_mul_of_nonneg_left hmR
      (mul_nonneg (show (0:ℝ) ≤ 6 by norm_num) (Nat.cast_nonneg C)),
    mul_le_mul_of_nonneg_left hnR
      (mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) (Nat.cast_nonneg core))]
