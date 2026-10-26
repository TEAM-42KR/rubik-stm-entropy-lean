import Mathlib
import RubikSTM.Definitions.WordBounds.CostEnvelope
import RubikSTM.Lemmas.GlobalWords.FiniteGlobalWordBound
import RubikSTM.Lemmas.Channel.Paired.UniversalCodebook
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

private theorem RubikCostBridge.eventually_block_large (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) :
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

private theorem RubikGrouping.mem_group_iff (m h : ℕ) (hh : 0 < h)
    (t : Fin h) (i : Fin m) :
    i ∈ RubikGrouping.group m h hh t ↔ RubikGrouping.groupOf m h hh i = t := by
  simp only [RubikGrouping.group, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem RubikGrouping.groups_cover (m h : ℕ) (hh : 0 < h) :
    Finset.univ.biUnion (RubikGrouping.group m h hh) = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, RubikGrouping.mem_group_iff]
  exact ⟨fun _ => trivial, fun _ => ⟨RubikGrouping.groupOf m h hh i, rfl⟩⟩

private theorem RubikGrouping.groups_disjoint (m h : ℕ) (hh : 0 < h)
    (s t : Fin h) (hst : s ≠ t) :
    Disjoint (RubikGrouping.group m h hh s) (RubikGrouping.group m h hh t) := by
  apply Finset.disjoint_left.mpr
  intro i his hit
  exact hst (((RubikGrouping.mem_group_iff m h hh s i).mp his).symm.trans
    ((RubikGrouping.mem_group_iff m h hh t i).mp hit))

private theorem RubikGrouping.group_card_exact (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikGrouping.group m h hh t).card = m / h + if t.val < m % h then 1 else 0 := by
  have he : (RubikGrouping.group m h hh t).card =
      Nat.count (fun x => x ≡ t.val [MOD h]) m := by
    rw [Nat.count_eq_card_filter_range]
    simp only [RubikGrouping.group, Finset.card_filter, RubikGrouping.groupOf, Fin.ext_iff]
    change (∑ i : Fin m, if i.val % h = t.val then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i % h = t.val then (1 : ℕ) else 0) m]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt t.isLt]
  rw [he, Nat.count_modEq_card m hh t.val, Nat.mod_eq_of_lt t.isLt]

private theorem RubikGrouping.group_card_floor_or_ceil (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikGrouping.group m h hh t).card = m / h ∨
      (RubikGrouping.group m h hh t).card = (m + h - 1) / h := by
  rw [RubikGrouping.group_card_exact]
  split_ifs with ht
  · right
    have hr : 0 < m % h := lt_of_le_of_lt (Nat.zero_le t.val) ht
    have hrem := Nat.mod_lt m hh
    have hdiv := Nat.div_add_mod m h
    have hsub : m + h - 1 + 1 = m + h := by omega
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith only [hdiv, hsub, hr]
    · nlinarith only [hdiv, hsub, hrem]
  · exact Or.inl (by omega)

private theorem RubikGrouping.sum_group_card (m h : ℕ) (hh : 0 < h) :
    ∑ t : Fin h, (RubikGrouping.group m h hh t).card = m := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
    (Finset.univ : Finset (Fin h)) (RubikGrouping.groupOf m h hh)
  simpa only [RubikGrouping.group, Finset.mem_univ, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin] using hf

private theorem RubikGrouping.group_card_real_le (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    ((RubikGrouping.group m h hh t).card : ℝ) ≤ (m : ℝ) / (h : ℝ) + 1 := by
  have hd : ((m / h : ℕ) : ℝ) ≤ (m : ℝ) / (h : ℝ) := Nat.cast_div_le
  rw [RubikGrouping.group_card_exact]
  split_ifs <;> push_cast <;> linarith only [hd]

private theorem RubikGrouping.same_group_pairs_bound (m h : ℕ) (hh : 0 < h) :
    ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
      (m : ℝ) ^ 2 / (h : ℝ) + (m : ℝ) := by
  have hcount : (RubikGrouping.sameGroupPairs m h hh).card ≤
      ∑ i : Fin m, (RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card := by
    unfold RubikGrouping.sameGroupPairs
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    rw [RubikGrouping.group, Finset.card_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i ≠ j ∧ RubikGrouping.groupOf m h hh i = RubikGrouping.groupOf m h hh j
    · rw [if_pos hij, if_pos hij.2.symm]
    · simp only [hij, if_false]
      positivity
  have hreal : ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
      ∑ i : Fin m, ((RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card : ℝ) := by
    exact_mod_cast hcount
  calc
    ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
        ∑ i : Fin m, ((RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card : ℝ) := hreal
    _ ≤ ∑ _i : Fin m, ((m : ℝ) / (h : ℝ) + 1) :=
      Finset.sum_le_sum (fun i _ => RubikGrouping.group_card_real_le m h hh _)
    _ = (m : ℝ) ^ 2 / (h : ℝ) + (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private theorem RubikGrouping.cross_group_products_bound (m h : ℕ) (hh : 0 < h) :
    RubikGrouping.crossGroupProducts m h hh ≤ (m : ℝ) ^ 2 / 2 := by
  let a : Fin h → ℝ := fun t => (RubikGrouping.group m h hh t).card
  have ha (t : Fin h) : 0 ≤ a t := Nat.cast_nonneg _
  have hsum : ∑ t : Fin h, a t = (m : ℝ) := by
    dsimp [a]
    exact_mod_cast RubikGrouping.sum_group_card m h hh
  let U : ℝ := ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => s < t), a s * a t
  let V : ℝ := ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => t < s), a s * a t
  have hswap : V = U := by
    dsimp [V, U]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
  have hle : U + V ≤ (m : ℝ) ^ 2 := by
    have htotal : (∑ s : Fin h, ∑ t : Fin h, a s * a t) = (m : ℝ) ^ 2 := by
      rw [← Finset.sum_mul_sum, hsum]
      ring
    rw [← htotal]
    dsimp [U, V]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    by_cases hst : s < t
    · have hts : ¬ t < s := not_lt.mpr hst.le
      simp only [hst, hts, if_true, if_false, add_zero, le_refl]
    · by_cases hts : t < s
      · simp only [hst, hts, if_true, if_false, zero_add, le_refl]
      · simp only [hst, hts, if_false, zero_add]
        exact mul_nonneg (ha _) (ha _)
  change U ≤ (m : ℝ) ^ 2 / 2
  rw [hswap] at hle
  linarith only [hle]
open RubikCostBridge

private theorem group_card_eq (n h : ℕ) (hh : 0 < h) (i : Fin h) :
    (RubikGlobalWord.depthGroup (RubikGlobalWord.balancedColour (n:=n) hh) i).card =
      (RubikGrouping.group (mNat n) h hh i).card := by
  have hinj : Function.Injective (RubikGlobal.depth (n:=n)) := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change a.val+1=b.val+1 at hv
    omega
  rw [RubikGlobalWord.depthGroup, Finset.card_image_of_injective _ hinj]
  rfl

private theorem same_count_eq (n h : ℕ) (hh : 0 < h) :
    RubikGlobalWord.sameCount (RubikGlobalWord.balancedColour (n:=n) hh) =
      (RubikGrouping.sameGroupPairs (mNat n) h hh).card := by
  classical
  let e : RubikGlobalWord.SamePair (RubikGlobalWord.balancedColour (n:=n) hh) ≃
      {p // p ∈ RubikGrouping.sameGroupPairs (mNat n) h hh} :=
    { toFun := fun p => ⟨p.val.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.val.property,p.property⟩⟩
      invFun := fun p => ⟨⟨p.val,(Finset.mem_filter.mp p.property).2.1⟩,
        (Finset.mem_filter.mp p.property).2.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

private theorem RubikCostBridge.partition_facts (n h : ℕ) (hh : 0 < h) :
    let f := RubikGlobalWord.balancedColour (n:=n) hh
    let r : Fin h → ℕ := fun i => (RubikGlobalWord.depthGroup f i).card
    (∀ i, mNat n / h ≤ r i ∧ r i ≤ mNat n / h + 1) ∧
    (∑ i, ∑ j, if i < j then (r i : ℝ) * r j else 0) ≤ m n ^ 2 / 2 ∧
    (RubikGlobalWord.sameCount f : ℝ) ≤ m n ^ 2 / (h : ℝ) + m n := by
  classical
  dsimp only
  simp_rw [group_card_eq]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [RubikGrouping.group_card_exact]
    split_ifs <;> omega
  · simpa only [RubikGrouping.crossGroupProducts, Finset.sum_filter, m] using
      RubikGrouping.cross_group_products_bound (mNat n) h hh
  · rw [same_count_eq]
    exact RubikGrouping.same_group_pairs_bound (mNat n) h hh

open RubikCostBridge

private theorem RubikCostBridge.rowCeil_eq_natCeil (r k : ℕ) (hk : 0 < k) :
    RubikRectangle.rowCeil r k = ⌈(r : ℝ) / (k : ℝ)⌉₊ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcR := (div_le_iff₀ hkR).mp (Nat.le_ceil ((r : ℝ)/(k : ℝ)))
  have hc : r ≤ ⌈(r : ℝ)/(k : ℝ)⌉₊ * k := by exact_mod_cast hcR
  apply Nat.le_antisymm
  · apply (Nat.div_le_iff_le_mul_add_pred hk).mpr
    rw [show r+k-1=r+(k-1) by omega, mul_comm k]
    exact Nat.add_le_add_right hc _
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hkR).mpr
    change (r : ℝ) ≤ (((r+k-1)/k : ℕ) : ℝ) * k
    have ht : (r+k-1) < ((r+k-1)/k+1)*k :=
      (Nat.div_lt_iff_lt_mul hk).mp (Nat.lt_succ_self _)
    have he : r+k-1+1 = r+k := by omega
    have hle : r ≤ ((r+k-1)/k)*k := by nlinarith
    exact_mod_cast hle

open Rubik

private theorem Rubik.word_walk_length_le {n : ℕ} (w : List (Rubik.Move n))
    (u v : Rubik.Position n) (h : Rubik.applyWord w u.val = v.val) :
    ∃ p : (Rubik.stmGraph n).Walk u v, p.length ≤ w.length := by
  classical
  induction w generalizing u with
  | nil =>
    have huv : u = v := Subtype.ext h
    subst v
    exact ⟨.nil, by simp⟩
  | cons m w ih =>
    by_cases hm : applyMove m u.val = u.val
    · have ht : applyWord w u.val = v.val := by
        simpa only [applyWord, List.foldl_cons, hm] using h
      obtain ⟨p, hp⟩ := ih u ht
      exact ⟨p, hp.trans (by simp)⟩
    · have hr : Reachable (applyMove m u.val) := by
        obtain ⟨wu, hwu⟩ := u.property
        refine ⟨wu ++ [m], ?_⟩
        calc
          applyWord (wu ++ [m]) (solved n) = applyMove m (applyWord wu (solved n)) := by
            simp [applyWord, List.foldl_append]
          _ = applyMove m u.val := congrArg (applyMove m) hwu
      let u' : Position n := ⟨applyMove m u.val, hr⟩
      have ha : (stmGraph n).Adj u u' := by
        refine ⟨?_, Or.inl ⟨m, rfl⟩⟩
        intro he
        exact hm (congrArg Subtype.val he).symm
      have ht : applyWord w u'.val = v.val := h
      obtain ⟨p, hp⟩ := ih u' ht
      refine ⟨.cons ha p, ?_⟩
      simpa only [SimpleGraph.Walk.length_cons, List.length_cons] using Nat.add_le_add_right hp 1

private theorem Rubik.edist_le_word_length {n : ℕ} (w : List (Rubik.Move n))
    (u v : Rubik.Position n) (h : Rubik.applyWord w u.val = v.val) :
    (Rubik.stmGraph n).edist u v ≤ (w.length : ℕ∞) := by
  obtain ⟨p, hp⟩ := Rubik.word_walk_length_le w u v h
  exact p.edist_le.trans (by exact_mod_cast hp)

private theorem Rubik.diameter_le_uniform_word_bound {n : ℕ} (B : ℝ)
    (h : ∀ u v : Rubik.Position n, ∃ w : List (Rubik.Move n),
      (w.length : ℝ) ≤ B ∧ Rubik.applyWord w u.val = v.val) :
    (Rubik.diameter n : ℝ) ≤ B := by
  letI : Nonempty (Rubik.Position n) := ⟨⟨Rubik.solved n, ⟨[], rfl⟩⟩⟩
  obtain ⟨u, v, huv⟩ := (Rubik.stmGraph n).exists_dist_eq_diam
  obtain ⟨w, hw, he⟩ := h u v
  have hd : (Rubik.stmGraph n).dist u v ≤ w.length := by
    have hx := Rubik.edist_le_word_length w u v he
    simpa only [SimpleGraph.dist, ENat.toNat_coe] using
      ENat.toNat_le_toNat hx (by simp)
  change (((Rubik.stmGraph n).diam : ℕ) : ℝ) ≤ B
  rw [← huv]
  exact (by exact_mod_cast hd : ((Rubik.stmGraph n).dist u v : ℝ) ≤ (w.length : ℝ)).trans hw

open Filter Topology RubikCostBridge

private theorem sum_group_pairs {A : Type*} [AddCommMonoid A] (H : ℕ)
    (F : RubikGlobalWord.GroupPair H → A) :
    (∑ p, F p) = ∑ i : Fin H, ∑ j : Fin H,
      if hij : i < j then F ⟨(i,j),hij⟩ else 0 := by
  classical
  let g (p : Fin H × Fin H) : A := if hp : p.1 < p.2 then F ⟨p,hp⟩ else 0
  have hs := Finset.sum_subtype (F := inferInstance) (p := fun p : Fin H × Fin H => p.1 < p.2) (Finset.univ.filter (fun p : Fin H × Fin H => p.1 < p.2))
    (by intro p; simp) g
  calc
    (∑ p, F p) = ∑ p : RubikGlobalWord.GroupPair H, g p.val := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [g,dif_pos p.property]
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin H × Fin H => p.1 < p.2), g p := hs.symm
    _ = _ := by
      rw [Finset.sum_filter,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [g,hij]

private theorem state_card_eq_q_sq : (Fintype.card RubikChannel.Paired.State : ℝ) = q ^ 2 := by
  have hc : Nat.card RubikChannel.Paired.State =
      Nat.card (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed) *
      Nat.card (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed) := Nat.card_prod _ _
  simp only [Nat.card_eq_fintype_card] at hc
  dsimp [q]
  rw [pow_two]
  exact_mod_cast hc

theorem proof_RubikCostBridge_actual_cost_envelope : CostEnvelope := by
  classical
  obtain ⟨C,R,hglobal⟩ := RubikGlobalWord.finite_global_word_bound
  intro η hη
  obtain ⟨L,hL,hL4,ρ,hρ,hLρ,K,hBook⟩ := RubikChannel.Paired.universalCodebook η hη
  refine ⟨L,ρ,R,C,6*(C:ℝ)+2*(RubikCore.cleanupBound:ℝ),by positivity,hρ,
    by positivity,by positivity,by positivity,?_,?_⟩
  · rw [state_card_eq_q_sq] at hLρ
    exact hLρ.le
  · filter_upwards [RubikCostBridge.eventually_block_large ρ hρ K,eventually_ge_atTop 1]
      with n hn hn1
    obtain ⟨hh,hscale⟩ := hn
    let H := hNat n
    let f := RubikGlobalWord.balancedColour (n:=n) hh
    let r : Fin H → ℕ := fun i => (RubikGlobalWord.depthGroup f i).card
    obtain ⟨hbal,hpairs,hcnt⟩ := RubikCostBridge.partition_facts n H hh
    change (∀ i, mNat n / H ≤ r i ∧ r i ≤ mNat n / H + 1) at hbal
    let k (p : RubikGlobalWord.GroupPair H) := block ρ (r p.val.2)
    have hk (p : RubikGlobalWord.GroupPair H) : K ≤ k p ∧ 0 < k p := by
      have ht := hscale (r p.val.2) (hbal p.val.2).1
      exact ⟨(le_max_left K 1).trans ht, (le_max_right K 1).trans ht⟩
    have hb (p : RubikGlobalWord.GroupPair H) := hBook (k p) (hk p).1
    choose B hcover hB using hb
    let Mnat (p : RubikGlobalWord.GroupPair H) : ℕ := ⌊Real.exp ((k p : ℝ)*ρ)⌋₊
    have hM (p : RubikGlobalWord.GroupPair H) (i : Fin L) : ((B p) i).card ≤ Mnat p := by
      apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
      exact hB p i
    let M (i j : Fin H) : ℝ := if hp : i < j then Mnat ⟨(i,j),hp⟩ else 0
    refine ⟨H,r,M,(RubikGlobalWord.sameCount f : ℝ),?_,hpairs,hcnt,?_,?_⟩
    · simpa only [m,h,Nat.floor_div_eq_div] using hbal
    · intro i j
      dsimp [M]
      split_ifs with hp
      · simpa only [Mnat,k,mul_comm] using Nat.floor_le (Real.exp_nonneg ((k ⟨(i,j),hp⟩ : ℝ)*ρ))
      · exact (Real.exp_pos _).le
    · have hd : d n ≤ ((∑ p : RubikGlobalWord.GroupPair H,
          RubikGlobalWord.rectangleCost R f k Mnat L p) +
          C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) +
          2*RubikCore.cleanupBound : ℕ) := by
        apply Rubik.diameter_le_uniform_word_bound
        intro c d
        obtain ⟨w,hw,he⟩ := hglobal n H f k Mnat L hL hL4 B (fun p => (hk p).2) hcover hM c d
        exact ⟨w,by exact_mod_cast hw,he⟩
      have hsum : (((∑ p : RubikGlobalWord.GroupPair H,
            RubikGlobalWord.rectangleCost R f k Mnat L p) : ℕ) : ℝ) =
          ∑ i : Fin H, ∑ j : Fin H, if i < j then
            (L : ℝ) * ((⌈(r i : ℝ) / (block ρ (r j) : ℝ)⌉₊ : ℝ) + 3) *
              ((r j : ℝ) + (R : ℝ) * ((block ρ (r j) : ℝ) + 1) * M i j)
            else 0 := by
        rw [Nat.cast_sum,sum_group_pairs]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i < j
        · simp only [hij, if_pos, dite_true]
          simp only [RubikGlobalWord.rectangleCost,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
            RubikCostBridge.rowCeil_eq_natCeil _ _ (hk ⟨(i,j),hij⟩).2]
          dsimp [k,r,M]
          simp only [hij, dite_true]
        · simp [hij]
      have hm_le : (mNat n : ℝ) ≤ n := by
        have : mNat n ≤ n := by dsimp [mNat]; omega
        exact_mod_cast this
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hcleanup : ((C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) +
          2*RubikCore.cleanupBound : ℕ) : ℝ) ≤
          (C:ℝ)*(RubikGlobalWord.sameCount f : ℝ) +
          (6*(C:ℝ)+2*(RubikCore.cleanupBound:ℝ))*n := by
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Fintype.card_fin]
        change (C:ℝ)*((RubikGlobalWord.sameCount f:ℝ)+6*(mNat n:ℝ)) +
          2*(RubikCore.cleanupBound:ℝ) ≤ _
        nlinarith [mul_le_mul_of_nonneg_left hm_le (show 0 ≤ 6*(C:ℝ) by positivity),
          mul_le_mul_of_nonneg_left hnR (show 0 ≤ 2*(RubikCore.cleanupBound:ℝ) by positivity)]
      have hd' : d n ≤ (((∑ p : RubikGlobalWord.GroupPair H,
            RubikGlobalWord.rectangleCost R f k Mnat L p) : ℕ) : ℝ) +
          ((C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) +
            2*RubikCore.cleanupBound : ℕ) : ℝ) := by
        simpa only [Nat.cast_add,add_assoc] using hd
      have ht := hd'.trans (add_le_add (le_refl _) hcleanup)
      rw [hsum] at ht
      simpa only [add_assoc] using ht
