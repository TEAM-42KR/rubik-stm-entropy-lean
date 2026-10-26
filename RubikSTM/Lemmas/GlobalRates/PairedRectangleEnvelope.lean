import RubikSTM.Proofs.GlobalRates.PairedRectangleEnvelope
import Mathlib
set_option autoImplicit false

theorem RubikGlobalRates.paired_rectangle_envelope :
    ∀ (q : ℝ) (d m h : ℕ → ℝ)
    (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ))
    (hd : ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, d n ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2
          / (2 * Real.log (m n / h n)) + C * (m n ^ 2 / h n + m n)), ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      d n * Real.log n / (n : ℝ) ^ 2 ≤ Real.log q / 4 + ε :=
  @proof_RubikGlobalRates_paired_rectangle_envelope
