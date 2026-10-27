import RubikSTM.Proofs.Solved.counting_lower_with_offset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

theorem RubikSolved.counting_lower_with_offset :
    ∀ (q a k : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ) (hcount : ∀ᶠ n : ℕ in Filter.atTop, q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ (d n + k)) (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, (1 / 4 : ℝ) * Real.log (q : ℝ) - ε ≤ (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
  @proof_RubikSolved_counting_lower_with_offset
