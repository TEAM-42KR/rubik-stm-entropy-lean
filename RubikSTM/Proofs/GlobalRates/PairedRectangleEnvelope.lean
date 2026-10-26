import Mathlib
set_option autoImplicit false

open Filter Topology

private theorem rgr_m_bounds (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) - 3 ≤ 2 * ((n / 2 - 1 : ℕ) : ℝ) ∧ 2 * ((n / 2 - 1 : ℕ) : ℝ) ≤ n := by
  have h1 : n ≤ 2 * (n / 2 - 1) + 3 := by omega
  have h2 : 2 * (n / 2 - 1) ≤ n := by omega
  have h1' : (n : ℝ) ≤ 2 * ((n / 2 - 1 : ℕ) : ℝ) + 3 := by exact_mod_cast h1
  have h2' : 2 * ((n / 2 - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
  exact ⟨by linarith, h2'⟩

private theorem rgr_eventually_m_facts (m : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ n ∧ (n : ℝ) / 4 ≤ m n ∧ m n ≤ n ∧ 1 < m n := by
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hb := rgr_m_bounds n (by omega)
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hm n]
  exact ⟨hn6, by linarith [hb.1], by linarith [hb.2], by linarith [hb.1]⟩

private theorem rgr_tendsto_m_div (m : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => m n / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (3 / 2) / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (3 / 2 : ℝ))
    rw [sub_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨h1, -⟩ := rgr_m_bounds n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    rw [hm n, show (1 / 2 : ℝ) - 3 / 2 / (n : ℝ) = ((n : ℝ) - 3) / 2 / n by field_simp]
    exact (div_le_div_iff_of_pos_right hnpos).mpr (by linarith)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨-, h2⟩ := rgr_m_bounds n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [hm n, div_le_iff₀ hnpos]
    linarith

private theorem rgr_tendsto_log_div_nat : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

private theorem rgr_tendsto_log_m_div_log (m : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (m n) / Real.log n) atTop (𝓝 1) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun n : ℕ => 1 - Real.log 4 / Real.log n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := Real.log 4)).div_atTop hlogn)
    rw [sub_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [rgr_eventually_m_facts m hm] with n hn
    obtain ⟨hn6, hm4, -, -⟩ := hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hle : Real.log (n / 4) ≤ Real.log (m n) := Real.log_le_log (by positivity) hm4
    rw [Real.log_div hnpos.ne' (by norm_num)] at hle
    rw [show (1 : ℝ) - Real.log 4 / Real.log n = (Real.log n - Real.log 4) / Real.log n by
      rw [sub_div, div_self hlogpos.ne']]
    exact (div_le_div_iff_of_pos_right hlogpos).mpr hle
  · filter_upwards [rgr_eventually_m_facts m hm] with n hn
    obtain ⟨hn6, -, hmn, hm1⟩ := hn
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    rw [div_le_one hlogpos]
    exact Real.log_le_log (by linarith) hmn

private theorem rgr_eventually_h_facts (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 0 < m n ∧ 1 ≤ h n ∧ Real.log (m n) ^ 3 ≤ h n ∧ 0 < Real.log (m n)
      ∧ 1 ≤ Real.log n ∧ Real.log (h n) ≤ Real.log 2 + 3 * Real.log (Real.log n) := by
  filter_upwards [rgr_eventually_m_facts m hm] with n hn
  obtain ⟨hn6, hm4, hmn, hm1⟩ := hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm0 : 0 < m n := by linarith
  have hlm : 0 < Real.log (m n) := Real.log_pos hm1
  have hlmn : Real.log (m n) ≤ Real.log n := Real.log_le_log hm0 hmn
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hln : 0 < Real.log (n : ℝ) := by linarith
  have hp : 0 < Real.log (m n) ^ 3 := pow_pos hlm 3
  have hceil1 : 0 < ⌈Real.log (m n) ^ 3⌉₊ := Nat.ceil_pos.mpr hp
  have hh1 : 1 ≤ h n := by rw [hh n]; exact_mod_cast hceil1
  have hh2 : Real.log (m n) ^ 3 ≤ h n := by rw [hh n]; exact Nat.le_ceil _
  have hh3 : h n < Real.log (m n) ^ 3 + 1 := by rw [hh n]; exact Nat.ceil_lt_add_one hp.le
  have hpow : Real.log (m n) ^ 3 ≤ Real.log n ^ 3 := pow_le_pow_left₀ hlm.le hlmn 3
  have hpow1 : 1 ≤ Real.log (n : ℝ) ^ 3 := one_le_pow₀ hlog1
  have hhle : h n ≤ 2 * Real.log n ^ 3 := by linarith
  have hlogh : Real.log (h n) ≤ Real.log 2 + 3 * Real.log (Real.log n) := by
    have h1 := Real.log_le_log (by linarith) hhle
    rw [Real.log_mul (by norm_num) (pow_pos hln 3).ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  exact ⟨hm0, hh1, hh2, hlm, hlog1, hlogh⟩

private theorem rgr_tendsto_log_h_div_log (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (h n) / Real.log n) atTop (𝓝 0) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun n : ℕ => (Real.log 2 + 3 * Real.log (Real.log n)) / Real.log n)
      atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := Real.log 2)).div_atTop hlogn
    have h2 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlogn
    have h3 := h1.add (h2.const_mul 3)
    rw [mul_zero, add_zero] at h3
    refine h3.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, id_eq]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [rgr_eventually_h_facts m h hm hh] with n hn
    obtain ⟨-, hh1, -, -, hlog1, -⟩ := hn
    exact div_nonneg (Real.log_nonneg hh1) (by linarith)
  · filter_upwards [rgr_eventually_h_facts m h hm hh] with n hn
    obtain ⟨-, -, -, -, hlog1, hlogh⟩ := hn
    exact (div_le_div_iff_of_pos_right (by linarith)).mpr hlogh

private theorem rgr_tendsto_log_quot_div_log (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (m n / h n) / Real.log n) atTop (𝓝 1) := by
  have hsub := (rgr_tendsto_log_m_div_log m hm).sub (rgr_tendsto_log_h_div_log m h hm hh)
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [rgr_eventually_h_facts m h hm hh] with n hn
  obtain ⟨hm0, hh1, -, -, -, -⟩ := hn
  rw [Real.log_div hm0.ne' (by linarith), sub_div]

private theorem rgr_tendsto_log_div_log_quot (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log n / Real.log (m n / h n)) atTop (𝓝 1) := by
  have hinv := (rgr_tendsto_log_quot_div_log m h hm hh).inv₀ one_ne_zero
  rw [inv_one] at hinv
  exact hinv.congr' (Eventually.of_forall fun n => inv_div _ _)

private theorem rgr_tendsto_log_div_h (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log n / h n) atTop (𝓝 0) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := (rgr_tendsto_log_m_div_log m hm).inv₀ one_ne_zero
  have hsq : Tendsto (fun n : ℕ => (Real.log (n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hlogn)
  have hprod := (hinv.pow 3).mul hsq
  rw [inv_one, one_pow, one_mul] at hprod
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod ?_ ?_
  · filter_upwards [rgr_eventually_h_facts m h hm hh] with n hn
    obtain ⟨-, hh1, -, -, hlog1, -⟩ := hn
    exact div_nonneg (by linarith) (by linarith)
  · filter_upwards [rgr_eventually_h_facts m h hm hh] with n hn
    obtain ⟨-, -, hh2, hlm, hlog1, -⟩ := hn
    have hln : 0 < Real.log (n : ℝ) := by linarith
    have hp : 0 < Real.log (m n) ^ 3 := pow_pos hlm 3
    have hl0 : Real.log (n : ℝ) ≠ 0 := hln.ne'
    have hm0 : Real.log (m n) ≠ 0 := hlm.ne'
    calc Real.log n / h n ≤ Real.log n / Real.log (m n) ^ 3 :=
          div_le_div_of_nonneg_left hln.le hp hh2
      _ = ((Real.log (m n) / Real.log n)⁻¹) ^ 3 * (Real.log n ^ 2)⁻¹ := by
          field_simp

theorem proof_RubikGlobalRates_paired_rectangle_envelope (q : ℝ) (d m h : ℕ → ℝ)
    (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ))
    (hd : ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, d n ≤ (Real.log (q ^ 2) + η + e n) * m n ^ 2
          / (2 * Real.log (m n / h n)) + C * (m n ^ 2 / h n + m n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      d n * Real.log n / (n : ℝ) ^ 2 ≤ Real.log q / 4 + ε := by
  intro ε hε
  obtain ⟨e, he, C, hC⟩ := hd (4 * ε) (by linarith)
  have hA := rgr_tendsto_m_div m hm
  have hB := rgr_tendsto_log_div_nat
  have hF := rgr_tendsto_log_div_log_quot m h hm hh
  have hG := rgr_tendsto_log_div_h m h hm hh
  have hlim := (((((tendsto_const_nhds (x := Real.log (q ^ 2) + 4 * ε)).add he).div_const 2).mul
      (hA.pow 2)).mul hF).add ((tendsto_const_nhds (x := C)).mul
        (((hA.pow 2).mul hG).add (hA.mul hB)))
  have hval : (Real.log (q ^ 2) + 4 * ε + 0) / 2 * (1 / 2 : ℝ) ^ 2 * 1
      + C * ((1 / 2 : ℝ) ^ 2 * 0 + 1 / 2 * 0) = Real.log q / 4 + ε / 2 := by
    rw [Real.log_pow]; push_cast; ring
  rw [hval] at hlim
  have hev := hlim.eventually (Iio_mem_nhds
    (show Real.log q / 4 + ε / 2 < Real.log q / 4 + ε by linarith))
  filter_upwards [hev, hC, eventually_ge_atTop 1] with n hn hdn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hid : ((Real.log (q ^ 2) + 4 * ε + e n) * m n ^ 2 / (2 * Real.log (m n / h n))
        + C * (m n ^ 2 / h n + m n)) * Real.log n / (n : ℝ) ^ 2 =
      (Real.log (q ^ 2) + 4 * ε + e n) / 2 * (m n / n) ^ 2 * (Real.log n / Real.log (m n / h n))
        + C * ((m n / n) ^ 2 * (Real.log n / h n) + m n / n * (Real.log n / n)) := by
    ring
  have hmono : d n * Real.log n / (n : ℝ) ^ 2 ≤ ((Real.log (q ^ 2) + 4 * ε + e n) * m n ^ 2
        / (2 * Real.log (m n / h n)) + C * (m n ^ 2 / h n + m n)) * Real.log n / (n : ℝ) ^ 2 :=
    (div_le_div_iff_of_pos_right (pow_pos hnpos 2)).mpr (mul_le_mul_of_nonneg_right hdn hlogn)
  rw [hid] at hmono
  exact (lt_of_le_of_lt hmono hn).le
