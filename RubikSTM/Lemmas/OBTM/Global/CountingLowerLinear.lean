import RubikSTM.Proofs.OBTM.Global.CountingLowerLinear
import Mathlib
set_option autoImplicit false

theorem RubikOBTM.Global.counting_lower_linear :
    ∀ (q a : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ) (hcount : ∀ᶠ n : ℕ in Filter.atTop, q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ d n) (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, (1 / 4 : ℝ) * Real.log (q : ℝ) - ε ≤ (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
  @proof_RubikOBTM_Global_counting_lower_linear
