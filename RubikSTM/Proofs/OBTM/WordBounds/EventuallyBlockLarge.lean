import RubikSTM.Definitions.WordBounds.CostEnvelope
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

open Filter Topology RubikCostBridge

private theorem m_eq_scalar (n : ℕ) : m n = ((n / 2 - 1 : ℕ) : ℝ) := by
  dsimp [m,mNat]
  congr 1
  omega

private theorem m_quotient_tendsto :
    Tendsto (fun n => m n / h n) atTop atTop := by
  have hlog := rr_tendsto_log_quot_atTop m h m_eq_scalar (fun _ => rfl)
  have hfacts := rgr_eventually_h_facts m h m_eq_scalar (fun _ => rfl)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [hfacts] with n hn
  have := Real.log_le_sub_one_of_pos (div_pos hn.1 (by linarith [hn.2.1] : 0 < h n))
  linarith

private theorem block_tendsto (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (block ρ) atTop atTop := by
  have hr : Tendsto (fun x : ℝ => (x - 3 * Real.log x) / x) atTop (nhds 1) := by
    have hg := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul 3)
    rw [mul_zero,sub_zero] at hg
    refine hg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp
    field_simp
  have hg : Tendsto (fun x : ℝ => x - 3 * Real.log x) atTop atTop := by
    have ht := Tendsto.pos_mul_atTop one_pos hr tendsto_id
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_mul_cancel₀ _ hx.ne'
  have hs : Tendsto (fun s : ℕ =>
      (Real.log (s : ℝ) - 3 * Real.log (Real.log (s : ℝ))) / ρ) atTop atTop :=
    (hg.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).atTop_div_const hρ
  exact tendsto_nat_floor_atTop.comp hs

theorem proof_RubikCostBridge_eventually_block_large (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < hNat n ∧
      ∀ s : ℕ, mNat n / hNat n ≤ s → max K 1 ≤ block ρ s := by
  have ht : Tendsto (fun n => mNat n / hNat n) atTop atTop := by
    simpa only [Function.comp_def,m,h,Nat.floor_div_eq_div] using
      tendsto_nat_floor_atTop.comp m_quotient_tendsto
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((block_tendsto ρ hρ).eventually (eventually_ge_atTop (max K 1)))
  have hh := rgr_eventually_h_facts m h m_eq_scalar (fun _ => rfl)
  filter_upwards [ht.eventually (eventually_ge_atTop N),hh] with n hn hh
  refine ⟨?_,fun s hs => hN s (hn.trans hs)⟩
  have hp : (0 : ℝ) < h n := by linarith [hh.2.1]
  change (0 : ℝ) < (hNat n : ℝ) at hp
  exact_mod_cast hp
