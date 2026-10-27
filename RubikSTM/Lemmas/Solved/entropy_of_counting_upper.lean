import RubikSTM.Proofs.Solved.entropy_of_counting_upper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

theorem RubikSolved.entropy_of_counting_upper :
    ∀ (q a k : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ) (u : ℕ → ℝ) (hcount : ∀ᶠ n : ℕ in Filter.atTop, q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ (d n + k)) (hu : Filter.Tendsto u Filter.atTop (nhds ((1 / 4 : ℝ) * Real.log (q : ℝ)))) (hle : ∀ᶠ n : ℕ in Filter.atTop, (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 ≤ u n), Filter.Tendsto (fun n : ℕ => (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2) Filter.atTop (nhds ((1 / 4 : ℝ) * Real.log (q : ℝ))) :=
  @proof_RubikSolved_entropy_of_counting_upper
