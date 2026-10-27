import Mathlib
import RubikSTM.Lemmas.OBTM.Global.CountingLowerLinear
set_option autoImplicit false
open Filter Topology

theorem proof_RubikSolved_counting_lower_with_offset (q a k : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ)
    (hcount : ∀ᶠ n : ℕ in Filter.atTop,
      q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ (d n + k))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 4 : ℝ) * Real.log (q : ℝ) - ε ≤
        (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hnat
  have hgap : Tendsto (fun n : ℕ => (k : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2)
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (hlog.div_atTop hnat)) using 1
    · ext n
      ring
    · simp
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (k : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 < ε / 2 :=
    (tendsto_order.1 hgap).2 _ (by linarith)
  have hlower := RubikOBTM.Global.counting_lower_linear q a hq ha (fun n => d n + k)
    hcount (ε / 2) (by linarith)
  filter_upwards [hlower, hsmall] with n hn hs
  have heq : ((d n + k : ℕ) : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 =
      (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 +
        (k : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 := by
    rw [Nat.cast_add]
    ring
  rw [heq] at hn
  linarith
