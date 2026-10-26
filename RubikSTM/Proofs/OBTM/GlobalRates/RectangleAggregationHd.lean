import Mathlib
import RubikSTM.Lemmas.OBTM.GlobalRates.RectCostUniform
set_option autoImplicit false

open Filter Topology

theorem proof_RubikGlobalRates_rectangle_aggregation_hd (q : ℝ) (d m h : ℕ → ℝ)
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
          + Cloc * cnt + Cexc * n) :
    ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, d n ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2
          / (2 * Real.log (m n / h n)) + C * (m n ^ 2 / h n + m n) := by
  intro η hη
  obtain ⟨L, ρ, C, Cloc, Cexc, hL, hρ, hC, hCloc, hCexc, hLρ, hev⟩ := hcost η hη
  obtain ⟨e, he, hA⟩ := RubikGlobalRates.rect_cost_uniform L ρ C hL hρ hC m h hm hh
  refine ⟨e, he, Cloc + 3 * Cexc, ?_⟩
  filter_upwards [hev, hA, eventually_ge_atTop 8] with n hn hAn hn8
  obtain ⟨G, r, M, cnt, hbal, hP, hcnt, hM, hd⟩ := hn
  obtain ⟨hℓ, hnonneg, hrect⟩ := hAn
  have hpair : (∑ i, ∑ j, if i < j then
            L * ((⌈(r i : ℝ) / (⌊(Real.log (r j) - 3 * Real.log (Real.log (r j))) / ρ⌋₊ : ℝ)⌉₊ : ℝ) + 3)
              * ((r j : ℝ) + C * ((⌊(Real.log (r j) - 3 * Real.log (Real.log (r j))) / ρ⌋₊ : ℝ) + 1)
                * M i j)
            else 0)
      ≤ ∑ i, ∑ j, if i < j then
          (L * ρ + e n) / Real.log (m n / h n) * ((r i : ℝ) * r j) else 0 := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs with hij
    · calc _ ≤ (L * ρ + e n) * (r i) * (r j) / Real.log (m n / h n) :=
            hrect (r i) (r j) (hbal i).1 (hbal j).1 (hbal j).2 (M i j) (hM i j)
        _ = _ := by ring
    · exact le_refl 0
  have hfac : (∑ i, ∑ j, if i < j then
          (L * ρ + e n) / Real.log (m n / h n) * ((r i : ℝ) * r j) else 0)
      = (L * ρ + e n) / Real.log (m n / h n)
          * ∑ i, ∑ j, if i < j then ((r i : ℝ) * r j) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  have hc : 0 ≤ (L * ρ + e n) / Real.log (m n / h n) := div_nonneg hnonneg hℓ.le
  have hhn : 0 ≤ h n := by rw [hh n]; positivity
  have hq0 : 0 ≤ m n ^ 2 / h n := div_nonneg (sq_nonneg _) hhn
  have hmain : (L * ρ + e n) / Real.log (m n / h n)
        * (∑ i, ∑ j, if i < j then ((r i : ℝ) * r j) else 0)
      ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2 / (2 * Real.log (m n / h n)) := by
    calc _ ≤ (L * ρ + e n) / Real.log (m n / h n) * (m n ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hP hc
      _ = (L * ρ + e n) * (m n ^ 2 / (2 * Real.log (m n / h n))) := by ring
      _ ≤ (Real.log (q ^ 2) + η + e n) * (m n ^ 2 / (2 * Real.log (m n / h n))) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (sq_nonneg _) (by linarith))
      _ = _ := by ring
  have hloc : Cloc * cnt ≤ Cloc * (m n ^ 2 / h n + m n) := mul_le_mul_of_nonneg_left hcnt hCloc
  have hnle : (n : ℝ) ≤ 3 * m n := by
    rw [hm n]
    have : n ≤ 3 * (n / 2 - 1) := by omega
    exact_mod_cast this
  have hexc : Cexc * n ≤ 3 * Cexc * (m n ^ 2 / h n + m n) := by
    nlinarith [mul_le_mul_of_nonneg_left hnle hCexc, mul_nonneg hCexc hq0]
  calc d n ≤ _ := hd
    _ ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2 / (2 * Real.log (m n / h n))
        + Cloc * (m n ^ 2 / h n + m n) + 3 * Cexc * (m n ^ 2 / h n + m n) := by
        linarith [hpair, hfac, hmain, hloc, hexc]
    _ = _ := by ring
