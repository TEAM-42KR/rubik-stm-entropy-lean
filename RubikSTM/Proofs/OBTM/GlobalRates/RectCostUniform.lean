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

private theorem rr_log_succ_le (t : ℝ) (ht : 1 ≤ t) : Real.log (t + 1) ≤ Real.log t + 1 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h1 : t + 1 ≤ Real.exp 1 * t := by nlinarith
  have h2 := Real.log_le_log (by linarith) h1
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp] at h2
  linarith

private theorem rr_tendsto_log_quot_atTop (m h : ℕ → ℝ) (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (m n / h n)) atTop atTop := by
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := Filter.Tendsto.pos_mul_atTop one_pos (rgr_tendsto_log_quot_div_log m h hm hh) hlogn
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  exact div_mul_cancel₀ _ hlog

private theorem rr_tendsto_Dratio (ρ : ℝ) :
    Tendsto (fun x : ℝ => (x - 3 * Real.log (x + 1) - ρ) / (x + 1)) atTop (𝓝 1) := by
  have hx1 : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_id
  have hlog : Tendsto (fun x : ℝ => Real.log (x + 1) / (x + 1)) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hx1
  have hc : Tendsto (fun x : ℝ => (1 + ρ) / (x + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx1
  have h3 := ((tendsto_const_nhds (x := (1 : ℝ))).sub hc).sub (hlog.const_mul 3)
  rw [sub_zero, mul_zero, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx1' : x + 1 ≠ 0 := by linarith
  field_simp <;> ring

private theorem rr_tendsto_P (ρ : ℝ) :
    Tendsto (fun x : ℝ => (x + 1) / ((x - 3 * Real.log (x + 1) - ρ) / ρ)) atTop (𝓝 ρ) := by
  have hq := (tendsto_const_nhds (x := ρ)).div (rr_tendsto_Dratio ρ) one_ne_zero
  rw [div_one] at hq
  refine hq.congr' (Eventually.of_forall fun x => ?_)
  simp only [Pi.div_apply, div_div_eq_mul_div]
  ring

private theorem rr_tendsto_R (ρ C : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun x : ℝ => C * ((x + 1) / ρ + 1) / x ^ 3) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  have h3 : Tendsto (fun x : ℝ => (x ^ 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num))
  have hsum := (h2.const_mul (C / ρ)).add (h3.const_mul (C * (1 / ρ + 1)))
  rw [mul_zero, mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp <;> ring

private theorem rr_tendsto_Q : Tendsto (fun t : ℝ => 4 * (Real.log t + 1) / t) atTop (𝓝 0) := by
  have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hs := (h1.add h2).const_mul 4
  rw [add_zero, mul_zero] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ht.ne'
  simp only [id_eq]
  field_simp <;> ring

private theorem rr_tendsto_F (L ρ C : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun t : ℝ => L * ((Real.log t + 1) / ((Real.log t - 3 * Real.log (Real.log t + 1) - ρ) / ρ)
        + 4 * (Real.log t + 1) / t) * (1 + C * ((Real.log t + 1) / ρ + 1) / Real.log t ^ 3))
      atTop (𝓝 (L * ρ)) := by
  have hP := (rr_tendsto_P ρ).comp Real.tendsto_log_atTop
  have hR := (rr_tendsto_R ρ C hρ).comp Real.tendsto_log_atTop
  have h := ((tendsto_const_nhds (x := L)).mul (hP.add rr_tendsto_Q)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add hR)
  rw [add_zero, add_zero, mul_one] at h
  exact h

private theorem rr_eventually_K (ρ : ℝ) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ Real.log t ∧ 0 < Real.log t - 3 * Real.log (Real.log t + 1) - ρ := by
  have hD := (rr_tendsto_Dratio ρ).comp Real.tendsto_log_atTop
  have h1 := hD.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have h2 := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [h1, h2] with t ht1 ht2
  refine ⟨ht2, ?_⟩
  have hpos : 0 < Real.log t + 1 := by linarith
  have ht1' : 1 / 2 < (Real.log t - 3 * Real.log (Real.log t + 1) - ρ) / (Real.log t + 1) := ht1
  have := (lt_div_iff₀ hpos).mp ht1'
  linarith

private theorem rr_rect_point (L ρ C t ℓ M : ℝ) (r s : ℕ) (hL : 0 ≤ L) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (ht1 : 1 ≤ t) (hu1 : 1 ≤ Real.log t)
    (hD : 0 < Real.log t - 3 * Real.log (Real.log t + 1) - ρ)
    (hr : t ≤ r) (hs : t ≤ s) (hs' : (s : ℝ) ≤ t + 1)
    (hℓ : 0 < ℓ) (hℓ' : ℓ ≤ Real.log t + 1)
    (hM : M ≤ Real.exp (ρ * ⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊)) :
    L * ((⌈(r : ℝ) / (⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ)⌉₊ : ℝ) + 3)
        * ((s : ℝ) + C * ((⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ) + 1) * M)
      ≤ L * ((Real.log t + 1) / ((Real.log t - 3 * Real.log (Real.log t + 1) - ρ) / ρ)
          + 4 * (Real.log t + 1) / t) * (1 + C * ((Real.log t + 1) / ρ + 1) / Real.log t ^ 3)
        * r * s / ℓ := by
  set k := ⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ with hk
  set u := Real.log t with hu
  set K := (u - 3 * Real.log (u + 1) - ρ) / ρ with hKdef
  have ht0 : 0 < t := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hls : u ≤ Real.log s := Real.log_le_log ht0 hs
  have hls' : Real.log s ≤ u + 1 := by
    have := Real.log_le_log hs0 hs'
    have := rr_log_succ_le t ht1
    linarith
  have hlls : Real.log (Real.log s) ≤ Real.log (u + 1) := Real.log_le_log (by linarith) hls'
  have hlls0 : 0 ≤ Real.log (Real.log s) := Real.log_nonneg (by linarith)
  have hKpos : 0 < K := div_pos hD hρ
  have hX0 : 0 ≤ (Real.log s - 3 * Real.log (Real.log s)) / ρ := by
    apply div_nonneg _ hρ.le
    linarith
  have hkle : (k : ℝ) ≤ (Real.log s - 3 * Real.log (Real.log s)) / ρ := Nat.floor_le hX0
  have hkgt : (Real.log s - 3 * Real.log (Real.log s)) / ρ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hKX : K ≤ (Real.log s - 3 * Real.log (Real.log s)) / ρ - 1 := by
    have e1 : K = (u - 3 * Real.log (u + 1)) / ρ - 1 := by
      rw [hKdef, sub_div, div_self hρ.ne']
    rw [e1]
    have : (u - 3 * Real.log (u + 1)) / ρ ≤ (Real.log s - 3 * Real.log (Real.log s)) / ρ :=
      (div_le_div_iff_of_pos_right hρ).mpr (by linarith)
    linarith
  have hkK : K < k := by linarith
  have hkpos : (0 : ℝ) < k := lt_trans hKpos hkK
  have hk1 : (k : ℝ) + 1 ≤ (u + 1) / ρ + 1 := by
    have : (Real.log s - 3 * Real.log (Real.log s)) / ρ ≤ (u + 1) / ρ :=
      (div_le_div_iff_of_pos_right hρ).mpr (by linarith)
    linarith
  have hρk : ρ * k ≤ Real.log s - 3 * Real.log (Real.log s) := by
    have := (le_div_iff₀ hρ).mp hkle
    linarith
  have hlogs_pos : 0 < Real.log s := by linarith
  have h3 : Real.exp (3 * Real.log (Real.log s)) = Real.log s ^ 3 := by
    rw [show (3 : ℝ) * Real.log (Real.log s) = ((3 : ℕ) : ℝ) * Real.log (Real.log s) by norm_num,
      Real.exp_nat_mul, Real.exp_log hlogs_pos]
  have hexp : M ≤ (s : ℝ) / Real.log s ^ 3 := by
    calc M ≤ Real.exp (ρ * k) := hM
      _ ≤ Real.exp (Real.log s - 3 * Real.log (Real.log s)) := Real.exp_le_exp.mpr hρk
      _ = (s : ℝ) / Real.log s ^ 3 := by rw [Real.exp_sub, Real.exp_log hs0, h3]
  have hu3 : 0 < u ^ 3 := pow_pos (by linarith) 3
  have hlogs3 : u ^ 3 ≤ Real.log s ^ 3 := pow_le_pow_left₀ (by linarith) hls 3
  have hsdiv : (s : ℝ) / Real.log s ^ 3 ≤ (s : ℝ) / u ^ 3 :=
    div_le_div_of_nonneg_left hs0.le hu3 hlogs3
  have hM' : M ≤ (s : ℝ) / u ^ 3 := hexp.trans hsdiv
  have hCk : 0 ≤ C * ((k : ℝ) + 1) := mul_nonneg hC (by positivity)
  have hsu : 0 ≤ (s : ℝ) / u ^ 3 := div_nonneg hs0.le hu3.le
  have hB1 : C * ((k : ℝ) + 1) * M ≤ C * ((u + 1) / ρ + 1) * ((s : ℝ) / u ^ 3) := by
    calc C * ((k : ℝ) + 1) * M ≤ C * ((k : ℝ) + 1) * ((s : ℝ) / u ^ 3) :=
          mul_le_mul_of_nonneg_left hM' hCk
      _ ≤ C * ((u + 1) / ρ + 1) * ((s : ℝ) / u ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk1 hC) hsu
  set B := 1 + C * ((u + 1) / ρ + 1) / u ^ 3 with hBdef
  have hB0 : 1 ≤ B := by
    have : 0 ≤ C * ((u + 1) / ρ + 1) / u ^ 3 :=
      div_nonneg (mul_nonneg hC (add_nonneg (div_nonneg (by linarith) hρ.le) zero_le_one)) hu3.le
    linarith
  have hB : (s : ℝ) + C * ((k : ℝ) + 1) * M ≤ (s : ℝ) * B := by
    have : C * ((u + 1) / ρ + 1) * ((s : ℝ) / u ^ 3) = (s : ℝ) * (C * ((u + 1) / ρ + 1) / u ^ 3) := by
      ring
    rw [hBdef]
    nlinarith
  have hceil : (⌈(r : ℝ) / (k : ℝ)⌉₊ : ℝ) < (r : ℝ) / k + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hr0.le hkpos.le)
  have hrk : (r : ℝ) / k ≤ (r : ℝ) / K := div_le_div_of_nonneg_left hr0.le hKpos hkK.le
  have hA : (⌈(r : ℝ) / (k : ℝ)⌉₊ : ℝ) + 3 ≤ (r : ℝ) / K + 4 := by linarith
  have hratio : 1 ≤ (u + 1) / ℓ := (le_div_iff₀ hℓ).mpr (by linarith)
  have hrt : 1 ≤ (r : ℝ) / t := (le_div_iff₀ ht0).mpr (by linarith)
  have hA' : (r : ℝ) / K + 4 ≤ (r : ℝ) / ℓ * ((u + 1) / K + 4 * (u + 1) / t) := by
    have e2 : (r : ℝ) / ℓ * ((u + 1) / K + 4 * (u + 1) / t)
        = (r : ℝ) / K * ((u + 1) / ℓ) + 4 * ((r : ℝ) / t * ((u + 1) / ℓ)) := by ring
    rw [e2]
    have i1 : (r : ℝ) / K ≤ (r : ℝ) / K * ((u + 1) / ℓ) :=
      le_mul_of_one_le_right (div_nonneg hr0.le hKpos.le) hratio
    have i2 : (1 : ℝ) ≤ (r : ℝ) / t * ((u + 1) / ℓ) := one_le_mul_of_one_le_of_one_le hrt hratio
    linarith
  have hsB : 0 ≤ (s : ℝ) * B := mul_nonneg hs0.le (by linarith)
  have hceil0 : (0 : ℝ) ≤ (⌈(r : ℝ) / (k : ℝ)⌉₊ : ℝ) + 3 := by positivity
  calc L * ((⌈(r : ℝ) / (k : ℝ)⌉₊ : ℝ) + 3) * ((s : ℝ) + C * ((k : ℝ) + 1) * M)
      ≤ L * ((⌈(r : ℝ) / (k : ℝ)⌉₊ : ℝ) + 3) * ((s : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hL hceil0)
    _ ≤ L * ((r : ℝ) / K + 4) * ((s : ℝ) * B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hL) hsB
    _ ≤ L * ((r : ℝ) / ℓ * ((u + 1) / K + 4 * (u + 1) / t)) * ((s : ℝ) * B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA' hL) hsB
    _ = L * ((u + 1) / K + 4 * (u + 1) / t) * B * r * s / ℓ := by ring

theorem proof_RubikGlobalRates_rect_cost_uniform (L ρ C : ℝ) (hL : 0 ≤ L) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (m h : ℕ → ℝ)
    (hm : ∀ n, m n = ((n / 2 - 1 : ℕ) : ℝ))
    (hh : ∀ n, h n = ((⌈Real.log (m n) ^ 3⌉₊ : ℕ) : ℝ)) :
    ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ᶠ n : ℕ in Filter.atTop,
      0 < Real.log (m n / h n) ∧ 0 ≤ L * ρ + e n ∧
      ∀ r s : ℕ, ⌊m n / h n⌋₊ ≤ r → ⌊m n / h n⌋₊ ≤ s → s ≤ ⌊m n / h n⌋₊ + 1 →
        ∀ M : ℝ, M ≤ Real.exp (ρ * ⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊) →
          L * ((⌈(r : ℝ) / (⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ)⌉₊ : ℝ) + 3)
            * ((s : ℝ) + C * ((⌊(Real.log s - 3 * Real.log (Real.log s)) / ρ⌋₊ : ℝ) + 1) * M)
          ≤ (L * ρ + e n) * r * s / Real.log (m n / h n) := by
  have hlq := rr_tendsto_log_quot_atTop m h hm hh
  have hfacts := rgr_eventually_h_facts m h hm hh
  have hx : Tendsto (fun n : ℕ => m n / h n) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlq
    filter_upwards [hfacts] with n hn
    obtain ⟨hm0, hh1, -, -, -, -⟩ := hn
    have := Real.log_le_sub_one_of_pos (div_pos hm0 (by linarith : (0 : ℝ) < h n))
    linarith
  have ha : Tendsto (fun n : ℕ => (⌊m n / h n⌋₊ : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1) hx)
    filter_upwards with n
    have := Nat.lt_floor_add_one (m n / h n)
    linarith
  set F : ℝ → ℝ := fun t => L * ((Real.log t + 1) / ((Real.log t - 3 * Real.log (Real.log t + 1) - ρ) / ρ)
        + 4 * (Real.log t + 1) / t) * (1 + C * ((Real.log t + 1) / ρ + 1) / Real.log t ^ 3) with hF
  have hFlim : Tendsto F atTop (𝓝 (L * ρ)) := rr_tendsto_F L ρ C hρ
  refine ⟨fun n => F (⌊m n / h n⌋₊ : ℝ) - L * ρ, ?_, ?_⟩
  · have := (hFlim.comp ha).sub_const (L * ρ)
    rw [sub_self] at this
    exact this
  · have hK := ha.eventually (rr_eventually_K ρ)
    have hge1 := ha.eventually (eventually_ge_atTop (1 : ℝ))
    filter_upwards [hK, hge1, hfacts] with n hKn h1n hn
    obtain ⟨hm0, hh1, -, -, -, -⟩ := hn
    obtain ⟨hu1, hD⟩ := hKn
    have hxpos : 0 < m n / h n := div_pos hm0 (by linarith)
    have htle : (⌊m n / h n⌋₊ : ℝ) ≤ m n / h n := Nat.floor_le hxpos.le
    have hlt : m n / h n < (⌊m n / h n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht0 : (0 : ℝ) < (⌊m n / h n⌋₊ : ℝ) := by linarith
    have hℓpos : 0 < Real.log (m n / h n) := by
      have := Real.log_le_log ht0 htle
      linarith
    have hℓle : Real.log (m n / h n) ≤ Real.log (⌊m n / h n⌋₊ : ℝ) + 1 := by
      have h1 : Real.log (m n / h n) ≤ Real.log ((⌊m n / h n⌋₊ : ℝ) + 1) :=
        Real.log_le_log hxpos hlt.le
      have h2 := rr_log_succ_le (⌊m n / h n⌋₊ : ℝ) h1n
      linarith
    have hFpos : 0 ≤ F (⌊m n / h n⌋₊ : ℝ) := by
      simp only [hF]
      have hK0 : 0 < (Real.log (⌊m n / h n⌋₊ : ℝ)
          - 3 * Real.log (Real.log (⌊m n / h n⌋₊ : ℝ) + 1) - ρ) / ρ := div_pos hD hρ
      apply mul_nonneg (mul_nonneg hL ?_) ?_
      · exact add_nonneg (div_nonneg (by linarith) hK0.le) (div_nonneg (by linarith) ht0.le)
      · have : 0 ≤ C * ((Real.log (⌊m n / h n⌋₊ : ℝ) + 1) / ρ + 1)
            / Real.log (⌊m n / h n⌋₊ : ℝ) ^ 3 :=
          div_nonneg (mul_nonneg hC (add_nonneg (div_nonneg (by linarith) hρ.le) zero_le_one))
            (pow_nonneg (by linarith) 3)
        linarith
    refine ⟨hℓpos, by linarith, ?_⟩
    intro r s hr hs hs' M hM
    have hr' : (⌊m n / h n⌋₊ : ℝ) ≤ r := by exact_mod_cast hr
    have hs1 : (⌊m n / h n⌋₊ : ℝ) ≤ s := by exact_mod_cast hs
    have hs2 : (s : ℝ) ≤ (⌊m n / h n⌋₊ : ℝ) + 1 := by exact_mod_cast hs'
    have key := rr_rect_point L ρ C (⌊m n / h n⌋₊ : ℝ) (Real.log (m n / h n)) M r s hL hρ hC
      h1n hu1 hD hr' hs1 hs2 hℓpos hℓle hM
    refine key.trans (le_of_eq ?_)
    simp only [hF]
    ring
