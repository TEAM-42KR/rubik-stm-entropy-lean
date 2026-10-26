import RubikSTM.Proofs.OBTM.GlobalRates.RectCostUniform
import Mathlib
set_option autoImplicit false

theorem RubikGlobalRates.rect_cost_uniform :
    ∀ (L ρ C : ℝ) (hL : 0 ≤ L) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (m h : ℕ → ℝ)
    (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)), ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ᶠ n : ℕ in Filter.atTop,
      0 < Real.log (m n / h n) ∧ 0 ≤ L * ρ + e n ∧
      ∀ r s : ℕ, ⌊m n / h n⌋₊ ≤ r → ⌊m n / h n⌋₊ ≤ s → s ≤ ⌊m n / h n⌋₊ + 1 →
        ∀ M : ℝ, M ≤ Real.exp (ρ * ⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊) →
          L * ((⌈(r : ℝ) / (⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ)⌉₊ : ℝ) + 3)
            * ((s : ℝ) + C * ((⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ) + 1) * M)
          ≤ (L * ρ + e n) * r * s / Real.log (m n / h n) :=
  @proof_RubikGlobalRates_rect_cost_uniform
