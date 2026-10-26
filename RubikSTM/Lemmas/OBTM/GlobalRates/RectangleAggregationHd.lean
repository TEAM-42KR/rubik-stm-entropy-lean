import RubikSTM.Proofs.OBTM.GlobalRates.RectangleAggregationHd
import Mathlib
set_option autoImplicit false

theorem RubikGlobalRates.rectangle_aggregation_hd :
    ∀ (q : ℝ) (d m h : ℕ → ℝ)
    (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ))
    (hcost : ∀ η : ℝ, 0 < η → ∃ L ρ C Cloc Cexc : ℝ, 0 ≤ L ∧ 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ Cloc ∧
      0 ≤ Cexc ∧ L * ρ ≤ Real.log (q ^ 2) + η ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∃ (G : ℕ) (r : Fin G → ℕ) (M : Fin G → Fin G → ℝ) (cnt : ℝ),
        (∀ i, ⌊m n / h n⌋₊ ≤ r i ∧ r i ≤ ⌊m n / h n⌋₊ + 1) ∧
        (∑ i, ∑ j, if i < j then ((r i : ℝ) * r j) else 0) ≤ m n ^ 2 / 2 ∧
        cnt ≤ m n ^ 2 / h n + m n ∧
        (∀ i j, M i j ≤ Real.exp (ρ * ⌊(Real.log (r j) - 3 * Real.log (Real.log (r j))) / ρ⌋₊)) ∧
        d n ≤ (∑ i, ∑ j, if i < j then
            L * ((⌈(r i : ℝ) / (⌊(Real.log (r j) - 3 * Real.log (Real.log (r j))) / ρ⌋₊ : ℝ)⌉₊ : ℝ) + 3)
              * ((r j : ℝ) + C * ((⌊(Real.log (r j) - 3 * Real.log (Real.log (r j))) / ρ⌋₊ : ℝ) + 1)
                * M i j)
            else 0)
          + Cloc * cnt + Cexc * n), ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, d n ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2
          / (2 * Real.log (m n / h n)) + C * (m n ^ 2 / h n + m n) :=
  @proof_RubikGlobalRates_rectangle_aggregation_hd
