import Mathlib
set_option autoImplicit false
open Filter Topology

theorem proof_RubikOBTM_Global_counting_lower_linear (q a : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ)
    (hcount : ∀ᶠ n : ℕ in Filter.atTop, q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ d n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 4 : ℝ) * Real.log (q : ℝ) - ε ≤
        (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
  let c : ℝ := (1 / 4 : ℝ) * Real.log (q : ℝ)
  let f : ℕ → ℝ := fun n =>
    c * (1 - 3 / (n : ℝ)) * (1 - 5 / (n : ℝ)) *
      (1 + Real.log ((a : ℝ) + 1) / Real.log (n : ℝ))⁻¹
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogNat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hthree : Tendsto (fun n : ℕ => (1 : ℝ) - 3 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (𝓝 3)).div_atTop hnat))
  have hfive : Tendsto (fun n : ℕ => (1 : ℝ) - 5 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5)).div_atTop hnat))
  have hlogdiv : Tendsto (fun n : ℕ => Real.log ((a : ℝ) + 1) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlogNat
  have hdenlim : Tendsto (fun n : ℕ => 1 + Real.log ((a : ℝ) + 1) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hlogdiv)
  have hlast : Tendsto (fun n : ℕ => (1 + Real.log ((a : ℝ) + 1) / Real.log (n : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using hdenlim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hf : Tendsto f atTop (𝓝 c) := by
    simpa [f] using ((hc.mul hthree).mul hfive).mul hlast
  have hevent : ∀ᶠ n : ℕ in atTop, c - ε < f n :=
    (tendsto_order.1 hf).1 (c - ε) (by linarith)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
  filter_upwards [hevent, eventually_ge_atTop (6 : ℕ), hcount] with n he hn hncount
  refine he.le.trans ?_
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlten : 0 < Real.log ((a : ℝ) + 1) := Real.log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
  have hden : 0 < Real.log (n : ℝ) + Real.log ((a : ℝ) + 1) := by positivity
  let k : ℕ := (n - 2) / 2
  have hk : n ≤ 2 * k + 3 := by dsimp [k]; omega
  have hk' : n ≤ 2 * (k - 1) + 5 := by dsimp [k]; omega
  have hkR : (n : ℝ) ≤ 2 * (k : ℝ) + 3 := by exact_mod_cast hk
  have hkR' : (n : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) + 5 := by exact_mod_cast hk'
  have hm : ((n : ℝ) - 3) * ((n : ℝ) - 5) / 4 ≤ ((k * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hm' := mul_le_mul
      (show (n : ℝ) - 3 ≤ 2 * (k : ℝ) by linarith)
      (show (n : ℝ) - 5 ≤ 2 * ((k - 1 : ℕ) : ℝ) by linarith)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 5)
      (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))
    nlinarith
  have hcountR : (q : ℝ) ^ (k * (k - 1)) ≤ ((a : ℝ) * (n : ℝ) + 1) ^ d n := by
    exact_mod_cast hncount
  have hlogs : ((k * (k - 1) : ℕ) : ℝ) * Real.log (q : ℝ) ≤
      (d n : ℝ) * Real.log ((a : ℝ) * (n : ℝ) + 1) := by
    simpa only [Real.log_pow] using
      Real.log_le_log (pow_pos hqpos _) hcountR
  have hlogbound : Real.log ((a : ℝ) * (n : ℝ) + 1) ≤
      Real.log (n : ℝ) + Real.log ((a : ℝ) + 1) := by
    have hb := Real.log_le_log
      (by positivity : (0 : ℝ) < (a : ℝ) * (n : ℝ) + 1)
      (show (a : ℝ) * (n : ℝ) + 1 ≤ ((a : ℝ) + 1) * (n : ℝ) by linarith)
    rw [Real.log_mul (by positivity : ((a : ℝ) + 1) ≠ 0) hnpos.ne'] at hb
    simpa [add_comm] using hb
  have hmain : (((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ) ≤
      (d n : ℝ) * (Real.log (n : ℝ) + Real.log ((a : ℝ) + 1)) :=
    (mul_le_mul_of_nonneg_right hm hlogq).trans
      (hlogs.trans (mul_le_mul_of_nonneg_left hlogbound (Nat.cast_nonneg _)))
  have hd : ((((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ)) /
      (Real.log (n : ℝ) + Real.log ((a : ℝ) + 1)) ≤ (d n : ℝ) :=
    (div_le_iff₀ hden).2 hmain
  calc
    f n = (((((n : ℝ) - 3) * ((n : ℝ) - 5) / 4) * Real.log (q : ℝ)) /
        (Real.log (n : ℝ) + Real.log ((a : ℝ) + 1))) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      dsimp [f, c]
      field_simp
      <;> ring
    _ ≤ (d n : ℝ) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hd (div_nonneg hln.le (sq_nonneg _))
    _ = (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by ring
