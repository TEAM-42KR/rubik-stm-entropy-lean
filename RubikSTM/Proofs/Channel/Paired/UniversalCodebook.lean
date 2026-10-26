import RubikSTM.Definitions.UniversalCodebooks.PathIndicator
import RubikSTM.Definitions.Codebook.Conditional.OverlapLaw
import Mathlib
import RubikSTM.Definitions.Channel.Paired.P
import RubikSTM.Definitions.Channel.EqualParitySubgroup
set_option autoImplicit false

open Filter Topology

private theorem RubikRates.exp_dominates_affine_nat (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) (A B : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → A * (k : ℝ) + B < c * Real.exp ((k : ℝ) * γ) := by
  let H : ℝ := |A| + |B| + 1
  have hden : 0 < c * γ ^ 2 := mul_pos hc (sq_pos_of_pos hγ)
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (2 * H / (c * γ ^ 2)))
  refine ⟨K, fun k hk => ?_⟩
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 1 < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hK hcast)
  have hlarge : 2 * H < (k : ℝ) * (c * γ ^ 2) :=
    (div_lt_iff₀ hden).mp (lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hK hcast))
  have hquad := Real.pow_div_factorial_le_exp ((k : ℝ) * γ)
    (mul_nonneg (Nat.cast_nonneg k) hγ.le) 2
  norm_num at hquad
  have hmul := mul_le_mul_of_nonneg_left hquad hc.le
  have hgrowth := mul_pos (show (0 : ℝ) < k by linarith)
    (show 0 < (k : ℝ) * (c * γ ^ 2) - 2 * H by linarith)
  have hA : A ≤ |A| := le_abs_self A
  have hB : B ≤ |B| := le_abs_self B
  have hAk := mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg k)
  have hBk := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ k by linarith) (abs_nonneg B)
  dsimp [H] at hgrowth
  nlinarith

private theorem RubikRates.exists_positive_multiple_four (P : ℕ → Prop) (hP : ∀ᶠ n : ℕ in Filter.atTop, P n) :
    ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ P L := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hP
  refine ⟨4 * (K + 1), by omega, dvd_mul_right _ _, hK _ (by omega)⟩

private theorem RubikRates.exists_four_layer_scale (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (A B : ℝ)
    (hB : 0 < B) : ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ N ≤ L ∧ A ≤ (L : ℝ) ∧
      (L : ℝ) * ρ ^ (L / 2) < B := by
  have hr2 : ρ ^ 2 < 1 := by nlinarith
  have ht := (tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hr2).const_mul 4
  have ht' : Tendsto (fun n : ℕ => ((4 * n : ℕ) : ℝ) * ρ ^ ((4 * n) / 2))
      atTop (𝓝 0) := by
    convert ht using 1
    · ext n
      rw [show 4 * n / 2 = 2 * n by omega]
      simp only [Nat.cast_mul, Nat.cast_ofNat, pow_mul]
      ring
    · norm_num
  have hb : ∀ᶠ n : ℕ in atTop,
      ((4 * n : ℕ) : ℝ) * ρ ^ ((4 * n) / 2) < B := ht'.eventually (gt_mem_nhds hB)
  have ha : ∀ᶠ n : ℕ in atTop, A ≤ ((4 * n : ℕ) : ℝ) := by
    have ha' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop A
    filter_upwards [ha'] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  obtain ⟨n, hnB, hnA, hnN, hn0⟩ :=
    (hb.and (ha.and ((eventually_ge_atTop N).and (eventually_ge_atTop 1)))).exists
  refine ⟨4 * n, by omega, dvd_mul_right _ _, by omega, hnA, hnB⟩

private theorem RubikRates.log_upper_envelope (q a x : ℝ) (hq : 0 < q) (ha : 1 / q ≤ a) (hx : 0 ≤ x) :
    0 < min a (1 / q + x) ∧ 0 ≤ Real.log (q * min a (1 / q + x)) ∧
      Real.log (q * min a (1 / q + x)) ≤ Real.log q + Real.log a ∧
      Real.log (q * min a (1 / q + x)) ≤ q * x := by
  have hinv : 0 < 1 / q := one_div_pos.mpr hq
  have ha0 : 0 < a := lt_of_lt_of_le hinv ha
  have hg : 0 < min a (1 / q + x) := lt_min ha0 (by linarith)
  have h1 : 1 ≤ q * min a (1 / q + x) := by
    have hl : 1 / q ≤ min a (1 / q + x) := le_min ha (by linarith)
    have := mul_le_mul_of_nonneg_left hl hq.le
    simpa [hq.ne'] using this
  refine ⟨hg, Real.log_nonneg h1, ?_, ?_⟩
  · have hm := Real.log_le_log (mul_pos hq hg)
      (mul_le_mul_of_nonneg_left (min_le_left a (1 / q + x)) hq.le)
    simpa [Real.log_mul hq.ne' ha0.ne'] using hm
  · have hm := Real.log_le_log (mul_pos hq hg)
      (mul_le_mul_of_nonneg_left (min_le_right a (1 / q + x)) hq.le)
    have hid : q * (1 / q + x) = 1 + q * x := by field_simp
    rw [hid] at hm
    have ht := Real.log_le_sub_one_of_pos (show 0 < 1 + q * x by positivity)
    linarith

private theorem RubikRates.log_lower_envelope (q x : ℝ) (hq : 0 < q) (hx : 0 ≤ x) (hsmall : q * x ≤ 1 / 2) :
    0 < 1 / q - x ∧ -2 * q * x ≤ Real.log q + Real.log (1 / q - x) ∧
      Real.log q + Real.log (1 / q - x) ≤ 0 := by
  have ht0 : 0 ≤ q * x := mul_nonneg hq.le hx
  have ht : 0 < 1 - q * x := by linarith
  have hm : 0 < 1 / q - x := by
    apply (sub_pos).mpr
    exact (lt_div_iff₀ hq).mpr (by nlinarith)
  have hid : q * (1 / q - x) = 1 - q * x := by field_simp
  have hlog : Real.log q + Real.log (1 / q - x) = Real.log (1 - q * x) := by
    rw [← Real.log_mul hq.ne' hm.ne', hid]
  refine ⟨hm, ?_, ?_⟩
  · have hi : (1 - q * x)⁻¹ ≤ 1 + 2 * (q * x) := by
      apply (inv_le_iff_one_le_mul₀ ht).mpr
      have hp := mul_nonneg ht0 (show 0 ≤ 1 - 2 * (q * x) by linarith)
      nlinarith
    have hl := Real.one_sub_inv_le_log_of_pos ht
    rw [hlog]
    linarith
  · rw [hlog]
    have hl := Real.log_le_log ht (show 1 - q * x ≤ 1 by linarith)
    simpa using hl

private theorem RubikRates.fixed_layer_overlap_slack (q ρ a η : ℝ) (hq : 1 < q) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 1 / q ≤ a) (ha1 : a < 1) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ 0 < 1 / q - ρ ^ L ∧
      ∃ α β r : ℝ, 0 < α ∧ 0 < β ∧ 0 < r ∧
        (L : ℝ) * r = Real.log q + η / 2 ∧
        α = (L : ℝ) * r + Real.log (1 / q - ρ ^ L) ∧ η / 4 ≤ α ∧
        ∀ j : ℕ, 1 ≤ j → j < L →
          β ≤ (j : ℝ) * r -
            Real.log (min a (1 / q + ρ ^ (L - j)) / (1 / q - ρ ^ L)) := by
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (one_div_pos.mpr hq0) ha
  let ε : ℝ := η / 2
  let d : ℝ := -Real.log a
  let h : ℝ := Real.log q + ε
  let u : ℝ := ε + d
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hd : 0 < d := neg_pos.mpr (Real.log_neg ha0 ha1)
  have hh : 0 < h := add_pos (Real.log_pos hq) hε
  have hu : 0 < u := add_pos hε hd
  have ht : Tendsto (fun n : ℕ => q * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul q
  obtain ⟨T, hTpow, hT1⟩ :=
    ((ht.eventually (gt_mem_nhds (show 0 < h / 8 by positivity))).and
      (eventually_ge_atTop 1)).exists
  let B : ℝ := min (1 / (2 * q))
    (min (ε / (4 * q)) (min (u / (8 * q)) (h / (16 * q))))
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : B * (2 * q) ≤ 1 := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * q)).mp
    exact min_le_left _ _
  have hBε : B * (4 * q) ≤ ε := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * q)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hBu : B * (8 * q) ≤ u := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * q)).mp
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hBh : B * (16 * q) ≤ h := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * q)).mp
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨L, hL, hL4, hLT, hLA, hLB⟩ :=
    RubikRates.exists_four_layer_scale ρ hρ0 hρ1 (2 * T) (4 * T * h / u) B hB
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpowL : ρ ^ L ≤ ρ ^ (L / 2) :=
    pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.div_le_self L 2)
  have hpoww : ρ ^ L ≤ (L : ℝ) * ρ ^ (L / 2) := by
    exact hpowL.trans (by simpa using
      mul_le_mul_of_nonneg_right hL1 (pow_nonneg hρ0.le (L / 2)))
  have hsmall : q * ρ ^ L ≤ 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_left (hpoww.trans_lt hLB) hq0
    nlinarith
  have hEε : 2 * q * ρ ^ L ≤ ε / 2 := by
    have hmul := mul_lt_mul_of_pos_left (hpoww.trans_lt hLB) hq0
    nlinarith
  have hEu : 2 * q * ρ ^ L ≤ u / 4 := by
    have hmul := mul_lt_mul_of_pos_left (hpoww.trans_lt hLB) hq0
    nlinarith
  have hEh : 2 * q * ρ ^ L ≤ h / 8 := by
    have hmul := mul_lt_mul_of_pos_left (hpoww.trans_lt hLB) hq0
    nlinarith
  have hTH : (T : ℝ) * h / L ≤ u / 4 := by
    have hmul := (div_le_iff₀ hu).mp hLA
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have htailmul : (L : ℝ) * (q * ρ ^ (L / 2) + 2 * q * ρ ^ L) ≤ h / 2 := by
    have hmul := mul_lt_mul_of_pos_left hLB (show 0 < 3 * q by positivity)
    have hp := mul_le_mul_of_nonneg_left hpowL
      (show 0 ≤ 2 * q * (L : ℝ) by positivity)
    nlinarith
  have htail : q * ρ ^ (L / 2) + 2 * q * ρ ^ L ≤ h / (2 * (L : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (L : ℝ))).mpr
    nlinarith
  let m : ℝ := 1 / q - ρ ^ L
  obtain ⟨hm, hmlo, hmhi⟩ := RubikRates.log_lower_envelope q (ρ ^ L) hq0
    (pow_nonneg hρ0.le L) hsmall
  let e : ℝ := -(Real.log q + Real.log m)
  have he : e ≤ 2 * q * ρ ^ L := by dsimp [e, m]; linarith
  have heε : e ≤ ε / 2 := he.trans hEε
  have heu : e ≤ u / 4 := he.trans hEu
  have heh : e ≤ h / 8 := he.trans hEh
  let r : ℝ := h / L
  let β : ℝ := min (u / 2) (min (h / 4) (h / (2 * (L : ℝ))))
  have hr : 0 < r := div_pos hh hL0
  have hβ : 0 < β := by dsimp [β]; positivity
  have hrL : (L : ℝ) * r = h := by dsimp [r]; field_simp
  have hβu : β ≤ u / 2 := min_le_left _ _
  have hβh : β ≤ h / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβL : β ≤ h / (2 * (L : ℝ)) := (min_le_right _ _).trans (min_le_right _ _)
  have halpha : η / 4 ≤ h + Real.log m := by
    dsimp [e, h, ε] at heε ⊢
    linarith
  refine ⟨L, hL, hL4, hm, h + Real.log m, β, r, lt_of_lt_of_le (by positivity) halpha,
    hβ, hr, hrL, ?_, halpha, ?_⟩
  · change h + Real.log m = (L : ℝ) * r + Real.log m
    rw [hrL]
  · intro j hj hjL
    let s : ℕ := L - j
    have hs1 : 1 ≤ s := by dsimp [s]; omega
    have hjs : (j : ℝ) + (s : ℝ) = L := by
      exact_mod_cast (show j + s = L by dsimp [s]; omega)
    obtain ⟨hg, hb0, hba, hbp⟩ := RubikRates.log_upper_envelope q a (ρ ^ s) hq0 ha
      (pow_nonneg hρ0.le s)
    let b : ℝ := Real.log (q * min a (1 / q + ρ ^ s))
    have hlog : Real.log (min a (1 / q + ρ ^ s) / m) = b + e := by
      rw [Real.log_div hg.ne' hm.ne']
      dsimp [b, e]
      rw [Real.log_mul hq0.ne' hg.ne']
      ring
    change β ≤ (j : ℝ) * r - Real.log (min a (1 / q + ρ ^ s) / m)
    rw [hlog]
    have hjr : (j : ℝ) * r = h - (s : ℝ) * r := by
      calc
        (j : ℝ) * r = ((j : ℝ) + (s : ℝ)) * r - (s : ℝ) * r := by ring
        _ = h - (s : ℝ) * r := by rw [hjs, hrL]
    by_cases hsT : s < T
    · have hsTc : (s : ℝ) ≤ T := by exact_mod_cast hsT.le
      have hTr : (T : ℝ) * r ≤ u / 4 := by simpa [r, mul_div_assoc] using hTH
      have hsr := mul_le_mul_of_nonneg_right hsTc hr.le
      have hid : h - (Real.log q + Real.log a) = u := by dsimp [h, u, d]; ring
      change b ≤ Real.log q + Real.log a at hba
      linarith only [hβu, hsr, hTr, hid, hba, heu, hjr]
    · have hTs : T ≤ s := by omega
      by_cases hsHalf : s ≤ L / 2
      · have hs2 : 2 * (s : ℝ) ≤ L := by exact_mod_cast (show 2 * s ≤ L by omega)
        have hmul := mul_le_mul_of_nonneg_right hs2 hr.le
        have hjhalf : h / 2 ≤ (j : ℝ) * r := by linarith only [hmul, hrL, hjr]
        have hps : ρ ^ s ≤ ρ ^ T := pow_le_pow_of_le_one hρ0.le hρ1.le hTs
        have hbsmall : b ≤ h / 8 := by
          exact hbp.trans ((mul_le_mul_of_nonneg_left hps hq0.le).trans hTpow.le)
        linarith only [hβh, hjhalf, hbsmall, heh]
      · have hhs : L / 2 ≤ s := by omega
        have hps : ρ ^ s ≤ ρ ^ (L / 2) := pow_le_pow_of_le_one hρ0.le hρ1.le hhs
        have hbsmall : b ≤ q * ρ ^ (L / 2) :=
          hbp.trans (mul_le_mul_of_nonneg_left hps hq0.le)
        have hjc : (1 : ℝ) ≤ j := by exact_mod_cast hj
        have hjrate := mul_le_mul_of_nonneg_right hjc hr.le
        have hrhalf : h / (2 * (L : ℝ)) = r / 2 := by dsimp [r]; ring
        rw [hrhalf] at htail hβL
        linarith only [hβL, hbsmall, hjrate, htail, he]

private theorem RubikRates.fixed_codebook_factor_absorbed (q η R : ℝ) (L : ℕ) (hη : 0 < η) (hR : 0 < R) (hL : 0 < L) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      R * Real.exp ((k : ℝ) * (Real.log q + η / 2) / (L : ℝ)) ≤
        Real.exp ((k : ℝ) * (Real.log q + η) / (L : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  let δ : ℝ := η / (2 * (L : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.log R / δ)
  refine ⟨K, fun k hk => ?_⟩
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hr : Real.log R ≤ (k : ℝ) * δ :=
    ((div_lt_iff₀ hδ).mp (hK.trans_le hcast)).le
  calc
    R * Real.exp ((k : ℝ) * (Real.log q + η / 2) / (L : ℝ)) =
        Real.exp (Real.log R + (k : ℝ) * (Real.log q + η / 2) / (L : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hR]
    _ ≤ Real.exp ((k : ℝ) * (Real.log q + η) / (L : ℝ)) := by
      apply Real.exp_le_exp.mpr
      calc
        Real.log R + (k : ℝ) * (Real.log q + η / 2) / (L : ℝ) ≤
            (k : ℝ) * δ + (k : ℝ) * (Real.log q + η / 2) / (L : ℝ) :=
          by linarith only [hr]
        _ = (k : ℝ) * (Real.log q + η) / (L : ℝ) := by dsimp [δ]; ring

private theorem RubikMoments.floor_exp_half_tail (r : ℝ) (hr : 0 < r) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.exp ((k : ℝ) * r) / 2 ≤ (⌊Real.exp ((k : ℝ) * r)⌋₊ : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.log 2 / r)
  refine ⟨K, fun k hk => ?_⟩
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hlin : Real.log 2 ≤ (k : ℝ) * r :=
    ((div_lt_iff₀ hr).mp (hK.trans_le hcast)).le
  have hexp : (2 : ℝ) ≤ Real.exp ((k : ℝ) * r) := by
    have ht := Real.exp_le_exp.mpr hlin
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at ht
    exact ht
  have hfloor := Nat.lt_floor_add_one (Real.exp ((k : ℝ) * r))
  linarith

private theorem RubikMoments.overlap_summand_bound (k j : ℕ) (r m g M β : ℝ) (hm : 0 < m) (hg : 0 < g)
    (hM : Real.exp ((k : ℝ) * r) / 2 ≤ M)
    (hslack : β ≤ (j : ℝ) * r - Real.log (g / m)) :
    (g / m) ^ k / M ^ j ≤ (2 : ℝ) ^ j * Real.exp (-(k : ℝ) * β) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hratio : 0 < g / m := div_pos hg hm
  have hMpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp ((k : ℝ) * r) / 2) hM j
  have hdiv : (g / m) ^ k / M ^ j ≤
      (g / m) ^ k / (Real.exp ((k : ℝ) * r) / 2) ^ j := by
    apply (div_le_div_iff₀ (pow_pos hM0 j) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left hMpow (pow_nonneg hratio.le k)
  have hpow : (g / m) ^ k = Real.exp ((k : ℝ) * Real.log (g / m)) := by
    rw [Real.exp_nat_mul, Real.exp_log hratio]
  calc
    (g / m) ^ k / M ^ j ≤
        (g / m) ^ k / (Real.exp ((k : ℝ) * r) / 2) ^ j := hdiv
    _ = (2 : ℝ) ^ j * Real.exp ((k : ℝ) * (Real.log (g / m) - (j : ℝ) * r)) := by
      have he : Real.exp ((k : ℝ) * (Real.log (g / m) - (j : ℝ) * r)) =
          Real.exp ((k : ℝ) * Real.log (g / m) - (j : ℝ) * ((k : ℝ) * r)) := by
        congr 1
        ring
      rw [hpow, div_pow, ← Real.exp_nat_mul, he, Real.exp_sub]
      field_simp
    _ ≤ (2 : ℝ) ^ j * Real.exp (-(k : ℝ) * β) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg k)
      nlinarith only [this]

private theorem RubikMoments.first_moment_lower (L k : ℕ) (r m M π ν α : ℝ) (hm : 0 < m)
    (hM : Real.exp ((k : ℝ) * r) / 2 ≤ M) (hπ : m ^ k ≤ π)
    (hν : ν = M ^ L * π) (hα : α = (L : ℝ) * r + Real.log m) :
    0 < ν ∧ Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L ≤ ν := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hπ0 : 0 < π := lt_of_lt_of_le (pow_pos hm k) hπ
  have hMpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp ((k : ℝ) * r) / 2) hM L
  have hprod := mul_le_mul hMpow hπ (pow_nonneg hm.le k) (pow_nonneg hM0.le L)
  have hmk : m ^ k = Real.exp ((k : ℝ) * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  have hid : (Real.exp ((k : ℝ) * r) / 2) ^ L * m ^ k =
      Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L := by
    rw [div_pow, ← Real.exp_nat_mul, hmk, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    rw [hα]
    ring
  refine ⟨by rw [hν]; positivity, ?_⟩
  rw [← hid, hν]
  exact hprod

private theorem RubikMoments.delta_ratio_bound (L k : ℕ) (r m M π ν Δ β : ℝ) (g : ℕ → ℝ)
    (hm : 0 < m) (hM : Real.exp ((k : ℝ) * r) / 2 ≤ M) (hπ : m ^ k ≤ π)
    (hν : ν = M ^ L * π) (hg : ∀ j ∈ Finset.Ico 1 L, 0 < g (L - j))
    (hslack : ∀ j ∈ Finset.Ico 1 L,
      β ≤ (j : ℝ) * r - Real.log (g (L - j) / m))
    (hΔ : 2 * Δ ≤ M ^ L * π * ∑ j ∈ Finset.Ico 1 L,
      (L.choose j : ℝ) * M ^ (L - j) * g (L - j) ^ k) :
    Δ / ν ^ 2 ≤ ((3 : ℝ) ^ L / 2) * Real.exp (-(k : ℝ) * β) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hπ0 : 0 < π := lt_of_lt_of_le (pow_pos hm k) hπ
  have hν0 : 0 < ν := by rw [hν]; positivity
  let E : ℝ := Real.exp (-(k : ℝ) * β)
  have hE : 0 < E := Real.exp_pos _
  have hterm : ∀ j ∈ Finset.Ico 1 L,
      (L.choose j : ℝ) * M ^ (L - j) * g (L - j) ^ k ≤
        ν * ((L.choose j : ℝ) * (2 : ℝ) ^ j * E) := by
    intro j hj
    have hjL : j ≤ L := (Finset.mem_Ico.mp hj).2.le
    have hp := RubikMoments.overlap_summand_bound k j r m (g (L - j)) M β
      hm (hg j hj) hM (hslack j hj)
    have hp' := (div_le_iff₀ (pow_pos hM0 j)).mp hp
    rw [div_pow] at hp'
    have hp'' := (div_le_iff₀ (pow_pos hm k)).mp hp'
    have hpow : M ^ L = M ^ (L - j) * M ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjL]
    have hpiM : M ^ L * m ^ k ≤ ν := by
      rw [hν]
      exact mul_le_mul_of_nonneg_left hπ (pow_nonneg hM0.le L)
    calc
      (L.choose j : ℝ) * M ^ (L - j) * g (L - j) ^ k ≤
          (L.choose j : ℝ) * M ^ (L - j) *
            (((2 : ℝ) ^ j * E) * M ^ j * m ^ k) :=
        mul_le_mul_of_nonneg_left hp'' (by positivity)
      _ = (M ^ L * m ^ k) * ((L.choose j : ℝ) * (2 : ℝ) ^ j * E) := by
        rw [hpow]
        ring
      _ ≤ ν * ((L.choose j : ℝ) * (2 : ℝ) ^ j * E) :=
        mul_le_mul_of_nonneg_right hpiM (by positivity)
  have hbinom : (∑ j ∈ Finset.range (L + 1), (L.choose j : ℝ) * (2 : ℝ) ^ j) =
      (3 : ℝ) ^ L := by
    simpa [show (2 : ℝ) + 1 = 3 by norm_num, mul_comm] using (add_pow (2 : ℝ) 1 L).symm
  have hsub : Finset.Ico 1 L ⊆ Finset.range (L + 1) := by
    intro j hj
    have := Finset.mem_Ico.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hsumchoose : (∑ j ∈ Finset.Ico 1 L, (L.choose j : ℝ) * (2 : ℝ) ^ j) ≤
      (3 : ℝ) ^ L := by
    rw [← hbinom]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro j hj hn; positivity)
  have hsum : (∑ j ∈ Finset.Ico 1 L,
      (L.choose j : ℝ) * M ^ (L - j) * g (L - j) ^ k) ≤ ν * ((3 : ℝ) ^ L * E) := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico 1 L, ν * ((L.choose j : ℝ) * (2 : ℝ) ^ j * E) :=
        Finset.sum_le_sum hterm
      _ = ν * ((∑ j ∈ Finset.Ico 1 L, (L.choose j : ℝ) * (2 : ℝ) ^ j) * E) := by
        rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ ν * ((3 : ℝ) ^ L * E) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsumchoose hE.le) hν0.le
  rw [← hν] at hΔ
  have hfinal := hΔ.trans (mul_le_mul_of_nonneg_left hsum hν0.le)
  apply (div_le_iff₀ (sq_pos_of_pos hν0)).mpr
  change Δ ≤ ((3 : ℝ) ^ L / 2 * E) * ν ^ 2
  nlinarith only [hfinal]

private theorem RubikMoments.second_moment_failure_bound (L k : ℕ) (ν Δ α β F : ℝ) (hν : 0 < ν)
    (hfirst : Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L ≤ ν)
    (hsecond : Δ / ν ^ 2 ≤ ((3 : ℝ) ^ L / 2) * Real.exp (-(k : ℝ) * β))
    (hF : F ≤ 1 / ν + 2 * Δ / ν ^ 2) :
    F ≤ ((2 : ℝ) ^ L + (3 : ℝ) ^ L) * Real.exp (-(k : ℝ) * min α β) := by
  have hfirst0 : 0 < Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L := by positivity
  have hinv := one_div_le_one_div_of_le hfirst0 hfirst
  have hrecip : 1 / ν ≤ (2 : ℝ) ^ L * Real.exp (-(k : ℝ) * α) := by
    calc
      1 / ν ≤ 1 / (Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L) := hinv
      _ = (2 : ℝ) ^ L * Real.exp (-(k : ℝ) * α) := by
        rw [neg_mul, Real.exp_neg]
        field_simp
  have hαmin : Real.exp (-(k : ℝ) * α) ≤ Real.exp (-(k : ℝ) * min α β) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (min_le_left α β) (Nat.cast_nonneg k)
    linarith only [ht]
  have hβmin : Real.exp (-(k : ℝ) * β) ≤ Real.exp (-(k : ℝ) * min α β) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (min_le_right α β) (Nat.cast_nonneg k)
    linarith only [ht]
  have hA := mul_le_mul_of_nonneg_left hαmin (by positivity : (0 : ℝ) ≤ 2 ^ L)
  have hB := mul_le_mul_of_nonneg_left hβmin (by positivity : (0 : ℝ) ≤ 3 ^ L)
  calc
    F ≤ 1 / ν + 2 * Δ / ν ^ 2 := hF
    _ = 1 / ν + 2 * (Δ / ν ^ 2) := by ring
    _ ≤ (2 : ℝ) ^ L * Real.exp (-(k : ℝ) * α) +
        (3 : ℝ) ^ L * Real.exp (-(k : ℝ) * β) := by
      linarith only [hrecip, hsecond]
    _ ≤ (2 : ℝ) ^ L * Real.exp (-(k : ℝ) * min α β) +
        (3 : ℝ) ^ L * Real.exp (-(k : ℝ) * min α β) := add_le_add hA hB
    _ = ((2 : ℝ) ^ L + (3 : ℝ) ^ L) * Real.exp (-(k : ℝ) * min α β) := by ring

private theorem RubikMoments.fixed_amplification_union_tail (q C γ : ℝ) (hq : 1 < q) (hC : 0 < C) (hγ : 0 < γ) :
    ∃ R : ℕ, 0 < R ∧ 2 * Real.log q < (R : ℝ) * γ ∧
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        q ^ (2 * k) * (C * Real.exp (-(k : ℝ) * γ)) ^ R < 1 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨R, hR⟩ := exists_nat_gt (max 0 (2 * Real.log q / γ))
  have hR0 : 0 < R := by
    have hc := lt_of_le_of_lt (le_max_left _ _) hR
    exact_mod_cast hc
  have hgap : 2 * Real.log q < (R : ℝ) * γ :=
    (div_lt_iff₀ hγ).mp (lt_of_le_of_lt (le_max_right _ _) hR)
  let d : ℝ := (R : ℝ) * γ - 2 * Real.log q
  have hd : 0 < d := sub_pos.mpr hgap
  obtain ⟨K, hK⟩ := exists_nat_gt ((R : ℝ) * Real.log C / d)
  refine ⟨R, hR0, hgap, K, fun k hk => ?_⟩
  have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hlin : (R : ℝ) * Real.log C < (k : ℝ) * d :=
    (div_lt_iff₀ hd).mp (hK.trans_le hcast)
  have hqpow : q ^ (2 * k) = Real.exp ((2 * k : ℕ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  have hCpow : C ^ R = Real.exp ((R : ℝ) * Real.log C) := by
    rw [Real.exp_nat_mul, Real.exp_log hC]
  have hid : q ^ (2 * k) * (C * Real.exp (-(k : ℝ) * γ)) ^ R =
      Real.exp ((R : ℝ) * Real.log C - (k : ℝ) * d) := by
    rw [mul_pow, hqpow, hCpow, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    dsimp [d]
    ring
  rw [hid]
  have := Real.exp_lt_exp.mpr (show (R : ℝ) * Real.log C - (k : ℝ) * d < 0 by linarith)
  simpa using this

private theorem RubikMoments.scalar_moment_bounds (L k : ℕ) (r m M π ν Δ α β F : ℝ)
    (g : ℕ → ℝ) (hm : 0 < m) (hM : Real.exp ((k : ℝ) * r) / 2 ≤ M)
    (hπ : m ^ k ≤ π) (hν : ν = M ^ L * π)
    (hα : α = (L : ℝ) * r + Real.log m) (hαpos : 0 < α) (hβpos : 0 < β)
    (hg : ∀ j ∈ Finset.Ico 1 L, 0 < g (L - j))
    (hslack : ∀ j ∈ Finset.Ico 1 L,
      β ≤ (j : ℝ) * r - Real.log (g (L - j) / m))
    (hΔ : 2 * Δ ≤ M ^ L * π * ∑ j ∈ Finset.Ico 1 L,
      (L.choose j : ℝ) * M ^ (L - j) * g (L - j) ^ k)
    (hF : F ≤ 1 / ν + 2 * Δ / ν ^ 2) :
    0 < ν ∧ Real.exp ((k : ℝ) * α) / (2 : ℝ) ^ L ≤ ν ∧
      Δ / ν ^ 2 ≤ ((3 : ℝ) ^ L / 2) * Real.exp (-(k : ℝ) * β) ∧
      0 < min α β ∧
      F ≤ ((2 : ℝ) ^ L + (3 : ℝ) ^ L) * Real.exp (-(k : ℝ) * min α β) := by
  obtain ⟨hν0, hfirst⟩ := RubikMoments.first_moment_lower L k r m M π ν α hm hM hπ hν hα
  have hsecond := RubikMoments.delta_ratio_bound L k r m M π ν Δ β g hm hM hπ hν hg hslack hΔ
  exact ⟨hν0, hfirst, hsecond, lt_min hαpos hβpos,
    RubikMoments.second_moment_failure_bound L k ν Δ α β F hν0 hfirst hsecond hF⟩

private theorem RubikCodebook.proper_overlap_card_le {L M : ℕ} (a : Fin L → Fin M) (j : ℕ) :
    Nat.card {b : Fin L → Fin M //
      (Finset.univ.filter (fun i => b i = a i)).card = j} ≤
      L.choose j * M ^ (L-j) := by
  classical
  let B := {b : Fin L → Fin M //
    (Finset.univ.filter (fun i => b i = a i)).card = j}
  let T := {S : Finset (Fin L) // S.card = j}
  let I := Σ S : T, ({i : Fin L // i ∉ S.val} → Fin M)
  let encode : B → I := fun b =>
    ⟨⟨Finset.univ.filter (fun i => b.val i = a i), b.property⟩,
      fun i => b.val i.val⟩
  let decode : I → (Fin L → Fin M) := fun t i =>
    if hi : i ∈ t.1.val then a i else t.2 ⟨i, hi⟩
  have hdecode (b : B) : decode (encode b) = b.val := by
    funext i
    change (if hi : i ∈ Finset.univ.filter (fun i => b.val i = a i)
      then a i else b.val i) = b.val i
    split_ifs with hi
    · exact (Finset.mem_filter.mp hi).2.symm
    · rfl
  have he : Function.Injective encode := by
    intro b c h
    apply Subtype.ext
    exact (hdecode b).symm.trans ((congrArg decode h).trans (hdecode c))
  have hcard (S : T) : Fintype.card {i : Fin L // i ∉ S.val} = L-j := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_coe, S.property]
  have hi : Fintype.card I = L.choose j * M ^ (L-j) := by
    simp [I, Fintype.card_sigma, Fintype.card_fun, hcard, T, Fintype.card_finset_len]
  change Nat.card B ≤ _
  rw [Nat.card_eq_fintype_card]
  rw [← hi]
  exact Fintype.card_le_of_injective encode he

private theorem RubikAggregate.path_Delta_le {L M : ℕ} {Ω : Type*} [Fintype Ω]
    (P : RubikJanson.FiniteLaw Ω) (X : (Fin L → Fin M) → Ω → ℝ)
    (π : ℝ) (g : ℕ → ℝ) (k : ℕ) (hπ : 0 ≤ π) (hg : ∀ s, 0 ≤ g s)
    (hjoint : ∀ a b, (RubikAggregate.overlapGraph L M).Adj a b →
      P.expect (fun ω => X a ω * X b ω) ≤
        π * g (L - RubikAggregate.overlapCount a b) ^ k) :
    2 * RubikJanson.Delta P X (RubikAggregate.overlapGraph L M) ≤
      (M : ℝ) ^ L * π * ∑ j ∈ Finset.Ico 1 L,
        (L.choose j : ℝ) * (M : ℝ) ^ (L - j) * g (L - j) ^ k := by
  classical
  let A := Fin L → Fin M
  let G := RubikAggregate.overlapGraph L M
  let c : A → A → ℕ := RubikAggregate.overlapCount
  have hproper (a b : A) (hab : G.Adj a b) : c a b ∈ Finset.Ico 1 L := by
    obtain ⟨hne, i, hi⟩ := hab
    have hcpos : 0 < c a b := by
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.symm⟩⟩
    have hcle : c a b ≤ L := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    have hcne : c a b ≠ L := by
      intro he
      have hcardeq : (Finset.univ.filter (fun i : Fin L => b i = a i)).card =
          (Finset.univ : Finset (Fin L)).card := by
        simpa only [c, RubikAggregate.overlapCount, Finset.card_univ, Fintype.card_fin] using he
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin L)), b i = a i :=
        Finset.card_filter_eq_iff.mp hcardeq
      apply hne
      funext t
      exact (hall t (Finset.mem_univ t)).symm
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hcard (a : A) (j : ℕ) :
      ((RubikJanson.neighbors G a).filter (fun b => c a b = j)).card ≤
        L.choose j * M ^ (L - j) := by
    have hs : (RubikJanson.neighbors G a).filter (fun b => c a b = j) ⊆
        Finset.univ.filter (fun b : A => c a b = j) := by
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, (Finset.mem_filter.mp hb).2⟩
    apply (Finset.card_le_card hs).trans
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, c,
      RubikAggregate.overlapCount] using RubikCodebook.proper_overlap_card_le a j
  have hrow (a : A) :
      (∑ b ∈ RubikJanson.neighbors G a, P.expect (fun ω => X a ω * X b ω)) ≤
        π * ∑ j ∈ Finset.Ico 1 L,
          (L.choose j : ℝ) * (M : ℝ) ^ (L - j) * g (L - j) ^ k := by
    have hmaps : ∀ b ∈ RubikJanson.neighbors G a, c a b ∈ Finset.Ico 1 L := by
      intro b hb
      exact hproper a b (Finset.mem_filter.mp hb).2
    calc
      (∑ b ∈ RubikJanson.neighbors G a, P.expect (fun ω => X a ω * X b ω)) ≤
          ∑ b ∈ RubikJanson.neighbors G a, π * g (L - c a b) ^ k := by
        apply Finset.sum_le_sum
        intro b hb
        exact hjoint a b (Finset.mem_filter.mp hb).2
      _ = ∑ j ∈ Finset.Ico 1 L,
          ∑ b ∈ (RubikJanson.neighbors G a).filter (fun b => c a b = j),
            π * g (L - c a b) ^ k :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ j ∈ Finset.Ico 1 L,
          ((L.choose j : ℝ) * (M : ℝ) ^ (L - j)) * (π * g (L - j) ^ k) := by
        apply Finset.sum_le_sum
        intro j hj
        have heq : (∑ b ∈ (RubikJanson.neighbors G a).filter (fun b => c a b = j),
            π * g (L - c a b) ^ k) =
              (((RubikJanson.neighbors G a).filter (fun b => c a b = j)).card : ℝ) *
                (π * g (L - j) ^ k) := by
          calc
            _ = ∑ b ∈ (RubikJanson.neighbors G a).filter (fun b => c a b = j),
                π * g (L - j) ^ k := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [(Finset.mem_filter.mp hb).2]
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        rw [heq]
        have hc : (((RubikJanson.neighbors G a).filter (fun b => c a b = j)).card : ℝ) ≤
            (L.choose j : ℝ) * (M : ℝ) ^ (L - j) := by exact_mod_cast hcard a j
        exact mul_le_mul_of_nonneg_right hc (mul_nonneg hπ (pow_nonneg (hg _) k))
      _ = π * ∑ j ∈ Finset.Ico 1 L,
          (L.choose j : ℝ) * (M : ℝ) ^ (L - j) * g (L - j) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hDelta : 2 * RubikJanson.Delta P X G =
      ∑ a : A, ∑ b ∈ RubikJanson.neighbors G a,
        P.expect (fun ω => X a ω * X b ω) := by
    simp only [RubikJanson.Delta]
    ring
  rw [hDelta]
  calc
    (∑ a : A, ∑ b ∈ RubikJanson.neighbors G a,
        P.expect (fun ω => X a ω * X b ω)) ≤
        ∑ _a : A, π * ∑ j ∈ Finset.Ico 1 L,
          (L.choose j : ℝ) * (M : ℝ) ^ (L - j) * g (L - j) ^ k :=
      Finset.sum_le_sum (fun a _ => hrow a)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, A, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

private theorem RubikAggregate.path_nu_eq {L M : ℕ} {Ω : Type*} [Fintype Ω]
    (P : RubikJanson.FiniteLaw Ω) (X : (Fin L → Fin M) → Ω → ℝ)
    (π : ℝ) (hmarginal : ∀ a, RubikJanson.mean P X a = π) :
    RubikJanson.nu P X = (M : ℝ) ^ L * π := by
  classical
  simp only [RubikJanson.nu, hmarginal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

private theorem RubikJanson.second_moment_multiply {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : RubikJanson.FiniteLaw Ω) (X : ι → Ω → ℝ) (G : SimpleGraph ι)
    (hX : RubikJanson.IsBernoulli X)
    (hpair : RubikJanson.NonedgeIndependent P X G) :
    RubikJanson.zeroProb P X * RubikJanson.nu P X ^ 2 ≤
      RubikJanson.nu P X + 2 * RubikJanson.Delta P X G := by
  classical
  let E := P.expect
  let p := RubikJanson.mean P X
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let ν := RubikJanson.nu P X
  have Econst (c : ℝ) : E (fun _ => c) = c := by
    change (∑ ω, P.weight ω * c) = c
    rw [← Finset.sum_mul, P.total, one_mul]
  have Eadd (f g : Ω → ℝ) :
      E (fun ω => f ω + g ω) = E f + E g := by
    simp only [E, RubikJanson.FiniteLaw.expect, mul_add, Finset.sum_add_distrib]
  have Esub (f g : Ω → ℝ) :
      E (fun ω => f ω - g ω) = E f - E g := by
    simp only [E, RubikJanson.FiniteLaw.expect, mul_sub, Finset.sum_sub_distrib]
  have Emul (c : ℝ) (f : Ω → ℝ) :
      E (fun ω => c * f ω) = c * E f := by
    change (∑ ω, P.weight ω * (c * f ω)) = c * ∑ ω, P.weight ω * f ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have Esum (f : ι → Ω → ℝ) :
      E (fun ω => ∑ i, f i ω) = ∑ i, E (f i) := by
    simp only [E, RubikJanson.FiniteLaw.expect, Finset.mul_sum]
    exact Finset.sum_comm
  have Emono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : E f ≤ E g := by
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω))
  have hp0 (i : ι) : 0 ≤ p i := by
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (P.nonneg ω) (by rcases hX i ω with h | h <;> simp [h])
  have hdiag (i : ι) : E (fun ω => X i ω * X i ω) = p i := by
    apply Finset.sum_congr rfl
    intro ω _
    rcases hX i ω with h | h <;> simp [h]
  have hES : E S = ν := Esum X
  have hES2 : E (fun ω => S ω ^ 2) =
      ∑ i, ∑ j, E (fun ω => X i ω * X j ω) := by
    calc
      E (fun ω => S ω ^ 2) =
          E (fun ω => ∑ i, ∑ j, X i ω * X j ω) := by
        congr 1
        funext ω
        simpa only [S, pow_two] using
          (Finset.sum_mul_sum Finset.univ Finset.univ
            (fun i => X i ω) (fun i => X i ω))
      _ = ∑ i, E (fun ω => ∑ j, X i ω * X j ω) := Esum _
      _ = ∑ i, ∑ j, E (fun ω => X i ω * X j ω) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Esum _
  have hterm (i j : ι) : E (fun ω => X i ω * X j ω) ≤
      p i * p j + (if i = j then p i else 0) +
        (if G.Adj i j then E (fun ω => X i ω * X j ω) else 0) := by
    by_cases hij : i = j
    · subst j
      have hloop : ¬ G.Adj i i := G.irrefl
      simp only [if_true, hloop, if_false, add_zero]
      rw [hdiag]
      nlinarith [sq_nonneg (p i)]
    · by_cases hadj : G.Adj i j
      · simp only [hij, if_false, hadj, if_true, add_zero]
        exact le_add_of_nonneg_left (mul_nonneg (hp0 i) (hp0 j))
      · have hind := hpair i j hij hadj
        change E (fun ω => X i ω * X j ω) = p i * p j at hind
        simp only [hij, if_false, hadj, add_zero]
        exact hind.le
  have hpp : (∑ i, ∑ j, p i * p j) = ν ^ 2 := by
    rw [← Finset.sum_mul_sum]
    change (∑ i, p i) * (∑ i, p i) = (∑ i, p i) ^ 2
    exact (pow_two _).symm
  have hdiagsum : (∑ i, ∑ j, if i = j then p i else (0 : ℝ)) = ν := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hadjsum : (∑ i, ∑ j, if G.Adj i j then
      E (fun ω => X i ω * X j ω) else 0) = 2 * RubikJanson.Delta P X G := by
    simp only [RubikJanson.Delta, RubikJanson.neighbors, Finset.sum_filter]
    ring
  have hsecond : E (fun ω => S ω ^ 2) ≤ ν ^ 2 + ν +
      2 * RubikJanson.Delta P X G := by
    rw [hES2]
    calc
      (∑ i, ∑ j, E (fun ω => X i ω * X j ω)) ≤
          ∑ i, ∑ j, (p i * p j + (if i = j then p i else 0) +
            (if G.Adj i j then E (fun ω => X i ω * X j ω) else 0)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = ν ^ 2 + ν + 2 * RubikJanson.Delta P X G := by
        simp_rw [Finset.sum_add_distrib]
        rw [hpp, hdiagsum, hadjsum]
  have hvariance : E (fun ω => (S ω - ν) ^ 2) =
      E (fun ω => S ω ^ 2) - ν ^ 2 := by
    calc
      E (fun ω => (S ω - ν) ^ 2) =
          E (fun ω => S ω ^ 2 - (2 * ν) * S ω + ν ^ 2) := by
        congr 1
        funext ω
        ring
      _ = E (fun ω => S ω ^ 2) - (2 * ν) * E S + ν ^ 2 := by
        rw [Eadd, Esub, Emul, Econst]
      _ = E (fun ω => S ω ^ 2) - ν ^ 2 := by rw [hES]; ring
  have hzero : RubikJanson.zeroProb P X * ν ^ 2 ≤
      E (fun ω => (S ω - ν) ^ 2) := by
    unfold RubikJanson.zeroProb RubikJanson.FiniteLaw.prob
    rw [mul_comm, ← Emul]
    apply Emono
    intro ω
    by_cases hz : ∀ i, X i ω = 0
    · have hS : S ω = 0 := by simp [S, hz]
      simp [hz, hS]
    · simp only [hz, if_false, mul_zero]
      exact sq_nonneg _
  change RubikJanson.zeroProb P X * ν ^ 2 ≤ ν + 2 * RubikJanson.Delta P X G
  rw [hvariance] at hzero
  linarith

private theorem RubikJanson.second_moment_zero {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : RubikJanson.FiniteLaw Ω) (X : ι → Ω → ℝ) (G : SimpleGraph ι)
    (hX : RubikJanson.IsBernoulli X)
    (hpair : RubikJanson.NonedgeIndependent P X G)
    (hν : 0 < RubikJanson.nu P X) :
    RubikJanson.zeroProb P X ≤ 1 / RubikJanson.nu P X +
      2 * RubikJanson.Delta P X G / RubikJanson.nu P X ^ 2 := by
  have h := RubikJanson.second_moment_multiply P X G hX hpair
  calc
    RubikJanson.zeroProb P X ≤
        (RubikJanson.nu P X + 2 * RubikJanson.Delta P X G) /
          RubikJanson.nu P X ^ 2 := (le_div_iff₀ (sq_pos_of_pos hν)).mpr h
    _ = 1 / RubikJanson.nu P X +
        2 * RubikJanson.Delta P X G / RubikJanson.nu P X ^ 2 := by
      field_simp

private theorem RubikJanson.uniform_event_card {Ω : Type*} [Fintype Ω] (hΩ : Nonempty Ω)
    (event : Ω → Prop) :
    (RubikJanson.uniformLaw hΩ).prob event =
      (Nat.card {ω : Ω // event ω} : ℝ) / Fintype.card Ω := by
  classical
  letI := hΩ
  unfold RubikJanson.FiniteLaw.prob RubikJanson.FiniteLaw.expect
  change (∑ ω, (1 / (Fintype.card Ω : ℝ)) * (if event ω then 1 else 0)) = _
  rw [← Finset.mul_sum]
  simp only [Finset.sum_boole]
  have hcard : (Finset.univ.filter event).card = Nat.card {ω : Ω // event ω} := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  ring

private theorem RubikCodebook.fixed_trials_cover {E Ω : Type*} [Fintype E] [Fintype Ω]
    (bad : E → Ω → Prop) (R : ℕ)
    (h : (∑ e : E, (Nat.card {ω : Ω // bad e ω}) ^ R) < (Fintype.card Ω) ^ R) :
    ∃ trials : Fin R → Ω, ∀ e : E, ∃ r : Fin R, ¬ bad e (trials r) := by
  classical
  by_contra hnone
  push_neg at hnone
  let I := Σ e : E, Fin R → {ω : Ω // bad e ω}
  let proj : I → (Fin R → Ω) := fun a r => (a.2 r).val
  have hsurj : Function.Surjective proj := by
    intro w
    obtain ⟨e, he⟩ := hnone w
    exact ⟨⟨e, fun r => ⟨w r, he r⟩⟩, rfl⟩
  have hcard := Fintype.card_le_of_surjective proj hsurj
  have hle : (Fintype.card Ω) ^ R ≤ ∑ e : E, (Nat.card {ω : Ω // bad e ω}) ^ R := by
    simpa [I, Nat.card_eq_fintype_card] using hcard
  exact (not_lt_of_ge hle) h

private theorem RubikJanson.uniform_fixed_trials_cover {E Ω : Type*} [Fintype E] [Fintype Ω]
    (hΩ : Nonempty Ω) (bad : E → Ω → Prop) (R : ℕ) (b : ℝ)
    (hb : 0 ≤ b)
    (hbad : ∀ e, (RubikJanson.uniformLaw hΩ).prob (bad e) ≤ b)
    (hsmall : (Fintype.card E : ℝ) * b ^ R < 1) :
    ∃ trials : Fin R → Ω, ∀ e : E, ∃ r : Fin R, ¬ bad e (trials r) := by
  classical
  letI := hΩ
  have hC : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardbad (e : E) : (Nat.card {ω : Ω // bad e ω} : ℝ) ≤
      b * (Fintype.card Ω : ℝ) := by
    apply (div_le_iff₀ hC).mp
    rw [← RubikJanson.uniform_event_card hΩ (bad e)]
    exact hbad e
  have hpower (e : E) : (Nat.card {ω : Ω // bad e ω} : ℝ) ^ R ≤
      (b * (Fintype.card Ω : ℝ)) ^ R := by
    exact pow_le_pow_left₀ (by positivity) (hcardbad e) R
  have hreal : (∑ e : E, (Nat.card {ω : Ω // bad e ω} : ℝ) ^ R) <
      (Fintype.card Ω : ℝ) ^ R := by
    calc
      _ ≤ ∑ _e : E, (b * (Fintype.card Ω : ℝ)) ^ R :=
        Finset.sum_le_sum (fun e _ => hpower e)
      _ = ((Fintype.card E : ℝ) * b ^ R) * (Fintype.card Ω : ℝ) ^ R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow]
        ring
      _ < (Fintype.card Ω : ℝ) ^ R := by
        simpa only [one_mul] using
          mul_lt_mul_of_pos_right hsmall (pow_pos hC R)
  apply RubikCodebook.fixed_trials_cover bad R
  exact_mod_cast hreal

private theorem UnionProofs.size {Letter : Type*} {k L R M : ℕ}
    (books : Fin R → RubikCodebook.Book Letter k L)
    (h : ∀ r i, (books r i).card ≤ M) (i : Fin L) :
    (RubikCodebook.layerwiseUnion books i).card ≤ R * M := by
  classical
  calc
    (RubikCodebook.layerwiseUnion books i).card ≤ ∑ r : Fin R, (books r i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r : Fin R, M := Finset.sum_le_sum (fun r _ => h r i)
    _ = R * M := by simp

private theorem UnionProofs.cover {Letter State : Type*} {k L R : ℕ}
    (act : Letter → Equiv.Perm State) (books : Fin R → RubikCodebook.Book Letter k L)
    (x y : Fin k → State)
    (h : ∃ r, RubikCodebook.CoversPair act (books r) x y) :
    RubikCodebook.CoversPair act (RubikCodebook.layerwiseUnion books) x y := by
  classical
  obtain ⟨r, w, hw, hxy⟩ := h
  refine ⟨w, ?_, hxy⟩
  intro i
  exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hw i⟩

private theorem RubikUniversal.sampleBook_card {Letter : Type*} {k L M : ℕ}
    (W : RubikUniversal.Sample Letter k L M) (i : Fin L) :
    (RubikUniversal.sampleBook W i).card ≤ M := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp)

private theorem RubikUniversal.coversPair_sample_iff {Letter State : Type*} {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (W : RubikUniversal.Sample Letter k L M)
    (x y : Fin k → State) :
    RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y ↔
      ∃ a : Fin L → Fin M, RubikJoint.endpointEvent act a x y W := by
  classical
  constructor
  · rintro ⟨w, hw, hxy⟩
    have hex : ∀ i : Fin L, ∃ t : Fin M, W (i, t) = w i := by
      intro i
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp (hw i)
      exact ⟨t, he⟩
    choose a ha using hex
    refine ⟨a, ?_⟩
    change RubikCodebook.eval act (fun i => W (i, a i)) x = y
    simpa only [ha] using hxy
  · rintro ⟨a, ha⟩
    refine ⟨fun i => W (i, a i), ?_, ha⟩
    intro i
    exact Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩

private theorem RubikUniversal.pathIndicator_bernoulli {Letter State : Type*} {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (x y : Fin k → State) :
    RubikJanson.IsBernoulli (RubikUniversal.pathIndicator (L := L) (M := M) act x y) := by
  classical
  intro a W
  unfold RubikUniversal.pathIndicator
  split <;> simp

private theorem RubikUniversal.sample_failure_eq_zeroProb {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (x y : Fin k → State) :
    (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
      (fun W => ¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y) =
      RubikJanson.zeroProb (RubikJoint.dictionaryLaw (C := Letter) k L M)
        (RubikUniversal.pathIndicator act x y) := by
  classical
  unfold RubikJanson.zeroProb RubikJanson.FiniteLaw.prob
  congr 1
  funext W
  have heq : (¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y) ↔
      ∀ a : Fin L → Fin M, RubikUniversal.pathIndicator act x y a W = 0 := by
    simp only [RubikUniversal.coversPair_sample_iff, not_exists,
      RubikUniversal.pathIndicator, ite_eq_right_iff, one_ne_zero, imp_false]
  by_cases hz : ∀ a : Fin L → Fin M, RubikUniversal.pathIndicator act x y a W = 0
  · simp only [heq, hz, if_true]
  · simp only [heq, hz, if_false]

open scoped Classical

private theorem RubikChannel.rowPermutation_eq_permMatrix {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) :
    RubikChannel.rowPermutation σ = σ.permMatrix ℝ := by
  ext x y
  simp [RubikChannel.rowPermutation]

private theorem RubikChannel.transition_doublyStochastic {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) :
    RubikChannel.transition μ act ∈ doublyStochastic ℝ X := by
  classical
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (μ.nonneg c)
    simp only [RubikChannel.rowPermutation]
    split <;> norm_num
  · intro x
    change (∑ y, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, eq_comm] using μ.total
  · intro y
    change (∑ x, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, Equiv.apply_eq_iff_eq_symm_apply] using μ.total

private theorem RubikChannel.run_eq_codebook_coordinate {C X : Type*} (act : C → Equiv.Perm X) {k L : ℕ}
    (w : Fin L → Fin k → C) (x : Fin k → X) (j : Fin k) :
    RubikChannel.run (fun _ : Fin L => act) (fun i => w i j) (x j) =
      RubikCodebook.eval act w x j := by
  unfold RubikChannel.run RubikCodebook.eval
  rw [show (List.ofFn (fun i : Fin L => act (w i j))) =
    (List.ofFn (fun i : Fin L => w i j)).map act from by
      simp only [List.map_ofFn, Function.comp_def]]
  rw [List.foldl_map]

private theorem RubikChannel.word_expect_succ {C : Type*} [Fintype C] (μ : RubikJanson.FiniteLaw C)
    (L : ℕ) (f : (Fin (L + 1) → C) → ℝ) :
    (RubikChannel.wordLaw μ (L + 1)).expect f =
      ∑ c, μ.weight c * (RubikChannel.wordLaw μ L).expect
        (fun w => f (Fin.cons c w)) := by
  classical
  unfold RubikJanson.FiniteLaw.expect
  change (∑ w : Fin (L + 1) → C, (∏ i, μ.weight (w i)) * f w) =
    ∑ c, μ.weight c * ∑ w : Fin L → C, (∏ i, μ.weight (w i)) * f (Fin.cons c w)
  rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => C)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [Finset.mul_sum, mul_assoc]
  rfl

private theorem RubikChannel.transition_mul_entry {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X)
    (A : Matrix X X ℝ) (x y : X) :
    (RubikChannel.transition μ act * A) x y =
      ∑ c, μ.weight c * A (act c x) y := by
  classical
  simp only [Matrix.mul_apply, RubikChannel.transition, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [RubikChannel.rowPermutation, mul_ite, ite_mul, eq_comm]

private theorem RubikChannel.run_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (L : ℕ)
    (act : Fin L → C → Equiv.Perm X) (x y : X) :
    (RubikChannel.wordLaw μ L).prob (fun w => RubikChannel.run act w x = y) =
      RubikChannel.wordMatrix μ act x y := by
  classical
  induction L generalizing x with
  | zero =>
      simp [RubikJanson.FiniteLaw.prob, RubikJanson.FiniteLaw.expect,
        RubikChannel.wordLaw, RubikChannel.run, RubikChannel.wordMatrix, Matrix.one_apply]
  | succ L ih =>
      have hr (c : C) (w : Fin L → C) :
          RubikChannel.run act (Fin.cons c w) x =
            RubikChannel.run (fun i => act i.succ) w (act 0 c x) := by
        simp [RubikChannel.run, List.ofFn_succ]
      unfold RubikJanson.FiniteLaw.prob
      rw [RubikChannel.word_expect_succ]
      simp_rw [hr]
      calc
        _ = ∑ c, μ.weight c * RubikChannel.wordMatrix μ
            (fun i => act i.succ) (act 0 c x) y := by
          apply Finset.sum_congr rfl
          intro c _
          apply congrArg (fun z : ℝ => μ.weight c * z)
          refine Eq.trans ?_ (ih (fun i => act i.succ) (act 0 c x))
          unfold RubikJanson.FiniteLaw.prob
          apply congrArg (RubikChannel.wordLaw μ L).expect
          funext w
          by_cases h : RubikChannel.run (fun i => act i.succ) w (act 0 c x) = y
          · simp only [h, if_true]
          · simp only [h, if_false]
        _ = _ := by
          simpa only [RubikChannel.wordMatrix, List.ofFn_succ, List.prod_cons] using
            (RubikChannel.transition_mul_entry μ (act 0)
              (RubikChannel.wordMatrix μ (fun i => act i.succ)) x y).symm

private theorem RubikChannel.frozen_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) {L : ℕ}
    (fixed : Fin L → Option C) (x y : X) :
    (RubikChannel.wordLaw μ L).prob (fun w =>
      RubikChannel.run (fun _ : Fin L => act) (RubikChannel.freeze fixed w) x = y) =
        RubikChannel.mixedMatrix μ act fixed x y := by
  classical
  letI : DecidableEq X := Classical.decEq X
  have hf (o : Option C) : RubikChannel.transition μ (fun c => act (o.getD c)) =
      o.elim (RubikChannel.transition μ act) (fun c => RubikChannel.rowPermutation (act c)) := by
    cases o with
    | none => rfl
    | some c =>
        ext a b
        change (∑ d, μ.weight d * RubikChannel.rowPermutation (act c) a b) = _
        rw [← Finset.sum_mul, μ.total, one_mul]
        rfl
  have hmatrix : RubikChannel.wordMatrix μ
      (fun i c => act ((fixed i).getD c)) = RubikChannel.mixedMatrix μ act fixed := by
    unfold RubikChannel.wordMatrix RubikChannel.mixedMatrix
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact hf (fixed i)
  rw [← hmatrix]
  exact RubikChannel.run_marginal μ L (fun i c => act ((fixed i).getD c)) x y

private theorem RubikChannel.mixedMatrix_worker {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) {L : ℕ}
    (fixed : Fin L → Option C) :
    RubikChannel.mixedMatrix μ act fixed =
      ((RubikChannel.mixedPermutations act fixed).map
        (fun t => t.elim (RubikChannel.transition μ act) (fun σ => σ.permMatrix ℝ))).prod := by
  classical
  have hinst : (inferInstance : DecidableEq X) = Classical.decEq X := Subsingleton.elim _ _
  cases hinst
  unfold RubikChannel.mixedMatrix RubikChannel.mixedPermutations
  rw [List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_def]
  cases fixed i with
  | none => rfl
  | some c => exact RubikChannel.rowPermutation_eq_permMatrix (act c)

private theorem RubikChannel.freezing_expectation {C : Type*} [Fintype C] (μ : RubikJanson.FiniteLaw C)
    (L : ℕ) (fixed : Fin L → Option C) (f : (Fin L → C) → ℝ) :
    (RubikChannel.wordLaw μ L).expect
        (fun w => if RubikChannel.Matches fixed w then f w else 0) =
      RubikChannel.fixedMass μ fixed * (RubikChannel.wordLaw μ L).expect
        (fun w => f (RubikChannel.freeze fixed w)) := by
  classical
  induction L with
  | zero =>
      have hf (w : Fin 0 → C) : RubikChannel.freeze fixed w = w := Subsingleton.elim _ _
      simp [RubikChannel.Matches, RubikChannel.fixedMass, hf]
  | succ L ih =>
      let t : Fin L → Option C := fun i => fixed i.succ
      have hm (c : C) (w : Fin L → C) :
          RubikChannel.Matches fixed (Fin.cons c w) ↔
          (∀ d, fixed 0 = some d → c = d) ∧ RubikChannel.Matches t w := by
        simp [RubikChannel.Matches, Fin.forall_fin_succ, t]
      have hf (c : C) (w : Fin L → C) :
          RubikChannel.freeze fixed (Fin.cons c w) =
            Fin.cons ((fixed 0).getD c) (RubikChannel.freeze t w) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hmass : RubikChannel.fixedMass μ fixed =
          (fixed 0).elim 1 μ.weight * RubikChannel.fixedMass μ t :=
        Fin.prod_univ_succ _
      rw [RubikChannel.word_expect_succ, hmass, RubikChannel.word_expect_succ]
      simp_rw [hf]
      cases h0 : fixed 0 with
      | none =>
          have hmnone (c : C) (w : Fin L → C) :
              RubikChannel.Matches fixed (Fin.cons c w) ↔ RubikChannel.Matches t w := by
            rw [hm, h0]
            simp
          simp only [hmnone, Option.elim_none, Option.getD_none, one_mul]
          calc
            _ = ∑ c, μ.weight c * (RubikChannel.fixedMass μ t *
                (RubikChannel.wordLaw μ L).expect
                  (fun w => f (Fin.cons c (RubikChannel.freeze t w)))) := by
              apply Finset.sum_congr rfl
              intro c _
              exact congrArg (fun z : ℝ => μ.weight c * z) (ih t (fun w => f (Fin.cons c w)))
            _ = _ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c _
              ring
      | some a =>
          have hmsome (c : C) (w : Fin L → C) :
              RubikChannel.Matches fixed (Fin.cons c w) ↔ c = a ∧ RubikChannel.Matches t w := by
            rw [hm, h0]
            simp
          simp only [hmsome, Option.elim_some, Option.getD_some]
          have hterm (c : C) : μ.weight c * (RubikChannel.wordLaw μ L).expect
                (fun w => if c = a ∧ RubikChannel.Matches t w then f (Fin.cons c w) else 0) =
              if c = a then μ.weight a * (RubikChannel.wordLaw μ L).expect
                (fun w => if RubikChannel.Matches t w then f (Fin.cons a w) else 0) else 0 := by
            by_cases hca : c = a
            · subst c
              simp
            · simp [hca, RubikJanson.FiniteLaw.expect]
          rw [show (∑ c, μ.weight c * (RubikChannel.wordLaw μ L).expect
              (fun w => if c = a ∧ RubikChannel.Matches t w then f (Fin.cons c w) else 0)) =
              μ.weight a * (RubikChannel.wordLaw μ L).expect
                (fun w => if RubikChannel.Matches t w then f (Fin.cons a w) else 0) by
            simp_rw [hterm]
            simp]
          rw [ih t (fun w => f (Fin.cons a w))]
          rw [← Finset.sum_mul, μ.total, one_mul]
          ring

private theorem RubikChannel.conditioned_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) {L : ℕ}
    (fixed : Fin L → Option C) (x y : X) :
    (RubikChannel.wordLaw μ L).prob (fun w => RubikChannel.Matches fixed w ∧
        RubikChannel.run (fun _ : Fin L => act) w x = y) =
      RubikChannel.fixedMass μ fixed * RubikChannel.mixedMatrix μ act fixed x y := by
  classical
  letI : DecidableEq X := Classical.decEq X
  calc
    _ = (RubikChannel.wordLaw μ L).expect (fun w => if RubikChannel.Matches fixed w
        then (if RubikChannel.run (fun _ : Fin L => act) w x = y then (1 : ℝ) else 0) else 0) := by
      unfold RubikJanson.FiniteLaw.prob
      apply congrArg (RubikChannel.wordLaw μ L).expect
      funext w
      by_cases hm : RubikChannel.Matches fixed w <;>
        by_cases he : RubikChannel.run (fun _ : Fin L => act) w x = y <;> simp [hm, he]
    _ = RubikChannel.fixedMass μ fixed * (RubikChannel.wordLaw μ L).expect
        (fun w => if RubikChannel.run (fun _ : Fin L => act)
          (RubikChannel.freeze fixed w) x = y then (1 : ℝ) else 0) :=
      RubikChannel.freezing_expectation μ L fixed
        (fun w => if RubikChannel.run (fun _ : Fin L => act) w x = y then (1 : ℝ) else 0)
    _ = _ := by
      apply congrArg (fun z : ℝ => RubikChannel.fixedMass μ fixed * z)
      exact RubikChannel.frozen_marginal μ act fixed x y

private theorem RubikChannel.array_event_product {C : Type*} [Fintype C] (μ : RubikJanson.FiniteLaw C)
    (k L : ℕ) (event : Fin k → (Fin L → C) → Prop) :
    (RubikChannel.arrayLaw μ k L).prob (fun w => ∀ j, event j (fun i => w i j)) =
      ∏ j, (RubikChannel.wordLaw μ L).prob (event j) := by
  classical
  unfold RubikJanson.FiniteLaw.prob RubikJanson.FiniteLaw.expect
  simp only [RubikChannel.arrayLaw, RubikChannel.wordLaw]
  rw [← (Equiv.piComm (fun _ : Fin k => fun _ : Fin L => C)).sum_comp]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Equiv.piComm_apply]
  rw [Finset.prod_comm]
  by_cases h : ∀ j, event j (w j)
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hz : (∏ j, (∏ i, μ.weight (w j i)) *
        (if event j (w j) then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    simpa only [h, if_false, mul_zero] using hz.symm

private theorem RubikChannel.codebook_frozen_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) {k L : ℕ}
    (fixed : Fin L → Fin k → Option C) (x y : Fin k → X) :
    (RubikChannel.arrayLaw μ k L).prob (fun w =>
      RubikCodebook.eval act (RubikChannel.freezeArray fixed w) x = y) =
      ∏ j, RubikChannel.mixedMatrix μ act (fun i => fixed i j) (x j) (y j) := by
  classical
  have hevent (w : Fin L → Fin k → C) :
      RubikCodebook.eval act (RubikChannel.freezeArray fixed w) x = y ↔
      ∀ j, RubikChannel.run (fun _ : Fin L => act)
        (RubikChannel.freeze (fun i => fixed i j) (fun i => w i j)) (x j) = y j := by
    constructor
    · intro h j
      have hh := congrFun h j
      rw [← RubikChannel.run_eq_codebook_coordinate] at hh
      exact hh
    · intro h
      funext j
      rw [← RubikChannel.run_eq_codebook_coordinate]
      exact h j
  calc
    _ = (RubikChannel.arrayLaw μ k L).prob (fun w => ∀ j,
        RubikChannel.run (fun _ : Fin L => act)
          (RubikChannel.freeze (fun i => fixed i j) (fun i => w i j)) (x j) = y j) := by
      unfold RubikJanson.FiniteLaw.prob
      apply congrArg (RubikChannel.arrayLaw μ k L).expect
      funext w
      simp only [hevent]
      by_cases h : ∀ j, RubikChannel.run (fun _ : Fin L => act)
          (RubikChannel.freeze (fun i => fixed i j) (fun i => w i j)) (x j) = y j
      · simp only [h, if_true]
      · simp only [h, if_false]
    _ = ∏ j, (RubikChannel.wordLaw μ L).prob (fun w =>
        RubikChannel.run (fun _ : Fin L => act)
          (RubikChannel.freeze (fun i => fixed i j) w) (x j) = y j) :=
      RubikChannel.array_event_product μ k L (fun (j : Fin k) (w : Fin L → C) =>
        RubikChannel.run (fun _ : Fin L => act)
          (RubikChannel.freeze (fun i => fixed i j) w) (x j) = y j)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact RubikChannel.frozen_marginal μ act (fun i => fixed i j) (x j) (y j)

private theorem RubikChannel.codebook_conditioned_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) {k L : ℕ}
    (fixed : Fin L → Fin k → Option C) (x y : Fin k → X) :
    (RubikChannel.arrayLaw μ k L).prob (fun w => RubikChannel.MatchesArray fixed w ∧
        RubikCodebook.eval act w x = y) =
      ∏ j, (RubikChannel.fixedMass μ (fun i => fixed i j) *
        RubikChannel.mixedMatrix μ act (fun i => fixed i j) (x j) (y j)) := by
  classical
  have hevent (w : Fin L → Fin k → C) :
      (RubikChannel.MatchesArray fixed w ∧ RubikCodebook.eval act w x = y) ↔
      ∀ j, RubikChannel.Matches (fun i => fixed i j) (fun i => w i j) ∧
        RubikChannel.run (fun _ : Fin L => act) (fun i => w i j) (x j) = y j := by
    constructor
    · rintro ⟨hm, he⟩ j
      refine ⟨fun i c hi => hm i j c hi, ?_⟩
      rw [RubikChannel.run_eq_codebook_coordinate]
      exact congrFun he j
    · intro h
      constructor
      · intro i j c hi
        exact (h j).1 i c hi
      · funext j
        rw [← RubikChannel.run_eq_codebook_coordinate]
        exact (h j).2
  calc
    _ = (RubikChannel.arrayLaw μ k L).prob (fun w => ∀ j,
        RubikChannel.Matches (fun i => fixed i j) (fun i => w i j) ∧
        RubikChannel.run (fun _ : Fin L => act) (fun i => w i j) (x j) = y j) := by
      unfold RubikJanson.FiniteLaw.prob
      apply congrArg (RubikChannel.arrayLaw μ k L).expect
      funext w
      by_cases h : RubikChannel.MatchesArray fixed w ∧ RubikCodebook.eval act w x = y
      · simp [h, (hevent w).mp h]
      · have hn := mt (hevent w).mpr h
        simp only [h, hn, if_false]
    _ = ∏ j, (RubikChannel.wordLaw μ L).prob (fun w =>
        RubikChannel.Matches (fun i => fixed i j) w ∧
        RubikChannel.run (fun _ : Fin L => act) w (x j) = y j) :=
      RubikChannel.array_event_product μ k L (fun (j : Fin k) (w : Fin L → C) =>
        RubikChannel.Matches (fun i => fixed i j) w ∧
        RubikChannel.run (fun _ : Fin L => act) w (x j) = y j)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact RubikChannel.conditioned_marginal μ act (fun i => fixed i j) (x j) (y j)

private theorem RubikChannel.codebook_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X)
    (k L : ℕ) (x y : Fin k → X) :
    (RubikChannel.arrayLaw μ k L).prob (fun w => RubikCodebook.eval act w x = y) =
      ∏ j, (RubikChannel.transition μ act ^ L) (x j) (y j) := by
  classical
  have hinst : (inferInstance : DecidableEq X) = Classical.decEq X := Subsingleton.elim _ _
  cases hinst
  have h := RubikChannel.codebook_frozen_marginal μ act
    (fun (_i : Fin L) (_j : Fin k) => none) x y
  change (RubikChannel.arrayLaw μ k L).prob
    (fun w => RubikCodebook.eval act w x = y) =
      ∏ j, RubikChannel.mixedMatrix μ act (fun _ : Fin L => none) (x j) (y j) at h
  simpa [RubikChannel.mixedMatrix, List.ofFn_const] using h

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

 theorem RubikConstruction.Matrix.residual_mul {n : Type*} [Fintype n] (A B J : Matrix n n ℝ)
    (hAJ : A * J = J) (hJB : J * B = J) (hJJ : J * J = J) :
    (A - J) * (B - J) = A * B - J := by
  rw [sub_mul, mul_sub, mul_sub, hAJ, hJB, hJJ, sub_self, sub_zero]

 theorem RubikConstruction.Matrix.uniform_absorption {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A ∈ doublyStochastic ℝ n) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    A * J = J ∧ J * A = J ∧ J * J = J := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change A * J = J ∧ J * A = J ∧ J * J = J
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : A * J = J := by
    ext i j
    change (∑ k, A i k * (Fintype.card n : ℝ)⁻¹) = _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hA i, one_mul]
  refine ⟨hr, ?_, ?_⟩
  · ext i j
    change (∑ k, (Fintype.card n : ℝ)⁻¹ * A k j) = _
    rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic hA j, mul_one]
  · ext i j
    change (∑ _ : n, (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹) = (Fintype.card n : ℝ)⁻¹
    simp [hc]

 theorem RubikConstruction.Matrix.stochastic_sandwich_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A P B : Matrix n n ℝ) (a : ℝ)
    (hA : A ∈ doublyStochastic ℝ n) (hB : B ∈ doublyStochastic ℝ n)
    (hP : ∀ u v, P u v ≤ a) (i j : n) : (A * P * B) i j ≤ a := by
  have hAP (v : n) : (A * P) i v ≤ a := by
    calc
      (A * P) i v = ∑ u, A i u * P u v := rfl
      _ ≤ ∑ u, A i u * a := Finset.sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_left (hP u v) (nonneg_of_mem_doublyStochastic hA)
      _ = a := by rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hA i, one_mul]
  calc
    (A * P * B) i j = ∑ v, (A * P) i v * B v j := rfl
    _ ≤ ∑ v, a * B v j := Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_right (hAP v) (nonneg_of_mem_doublyStochastic hB)
    _ = a := by rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic hB j, mul_one]

 theorem RubikConstruction.Matrix.list_absorption {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) (l : List (Matrix n n ℝ))
    (h : ∀ A ∈ l, A * J = J ∧ J * A = J) :
    l.prod * J = J ∧ J * l.prod = J := by
  induction l with
  | nil => simp
  | cons A l ih =>
    have hA := h A (by simp)
    have ht := ih (fun B hB => h B (by simp [hB]))
    constructor
    · simpa only [List.prod_cons, mul_assoc, ht.1] using hA.1
    · simpa only [List.prod_cons, ← mul_assoc, hA.2] using ht.2

 theorem RubikConstruction.Matrix.residual_list_prod {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) (hJJ : J * J = J) (l : List (Matrix n n ℝ))
    (hl : l ≠ []) (h : ∀ A ∈ l, A * J = J ∧ J * A = J) :
    (l.map (fun A => A - J)).prod = l.prod - J := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
    have hA := h A (by simp)
    have ht : ∀ B ∈ l, B * J = J ∧ J * B = J :=
      fun B hB => h B (by simp [hB])
    cases l with
    | nil => simp
    | cons B l =>
      rw [List.map_cons, List.prod_cons, ih (by simp) ht, List.prod_cons]
      exact RubikConstruction.Matrix.residual_mul A (B :: l).prod J hA.1 (RubikConstruction.Matrix.list_absorption J _ ht).2 hJJ

 theorem RubikConstruction.Matrix.uniform_center_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖(1 : Matrix n n ℝ) - J‖ ≤ 1 := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖(1 : Matrix n n ℝ) - J‖ ≤ 1
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJJ : J * J = J := by
    ext i j
    change (∑ _ : n, (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹) = (Fintype.card n : ℝ)⁻¹
    simp [hc]
  have hstar : star J = J := by
    ext i j
    change star (J j i) = J i j
    simp [J]
  have hproj : IsStarProjection J := ⟨hJJ, hstar⟩
  exact IsStarProjection.norm_le _ hproj.one_sub

 theorem RubikConstruction.Matrix.entry_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ n := EuclideanSpace.single j 1
  have he : (Matrix.toEuclideanCLM (𝕜 := ℝ) A e) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A e) i‖ := congrArg norm he.symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A e‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ * ‖e‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm e
    _ = ‖A‖ := by simp [e]

 theorem RubikConstruction.Matrix.mean_zero_residual_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcontract : ∀ x : EuclideanSpace ℝ n, (∑ i, x i) = 0 →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P x‖ ≤ lam * ‖x‖) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖P - J‖ ≤ lam := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  let C : Matrix n n ℝ := 1 - J
  change ‖P - J‖ ≤ lam
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJx (x : EuclideanSpace ℝ n) (i : n) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) J x) i =
        (Fintype.card n : ℝ)⁻¹ * ∑ j, x j := by
    change (∑ j, (Fintype.card n : ℝ)⁻¹ * x j) = _
    rw [← Finset.mul_sum]
  have hcenter0 (x : EuclideanSpace ℝ n) :
      (∑ i, (Matrix.toEuclideanCLM (𝕜 := ℝ) C x) i) = 0 := by
    have heq : Matrix.toEuclideanCLM (𝕜 := ℝ) C x =
        x - Matrix.toEuclideanCLM (𝕜 := ℝ) J x := by simp [C, map_sub]
    rw [heq]
    change (∑ i, (x i - (Matrix.toEuclideanCLM (𝕜 := ℝ) J x) i)) = 0
    simp_rw [hJx]
    rw [Finset.sum_sub_distrib]
    simp [hc]
  have hPC : P * C = P - J := by
    dsimp only [C]
    rw [mul_sub, mul_one, (RubikConstruction.Matrix.uniform_absorption P hP).1]
  have hCnorm : ‖C‖ ≤ 1 := RubikConstruction.Matrix.uniform_center_norm
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ hlam
  intro x
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J) x‖ =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P
          (Matrix.toEuclideanCLM (𝕜 := ℝ) C x)‖ := by rw [← hPC, map_mul]; rfl
    _ ≤ lam * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) C x‖ := hcontract _ (hcenter0 x)
    _ ≤ lam * ‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ hlam
      calc
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) C x‖ ≤ ‖C‖ * ‖x‖ :=
          (Matrix.toEuclideanCLM (𝕜 := ℝ) C).le_opNorm x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hCnorm (norm_nonneg x)
        _ = ‖x‖ := one_mul _

 theorem RubikConstruction.Matrix.permutation_residual_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (σ : Equiv.Perm n) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖σ.permMatrix ℝ - J‖ ≤ 1 := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖σ.permMatrix ℝ - J‖ ≤ 1
  have hUJ : σ.permMatrix ℝ * J = J :=
    (RubikConstruction.Matrix.uniform_absorption (σ.permMatrix ℝ) permMatrix_mem_doublyStochastic).1
  calc
    ‖σ.permMatrix ℝ - J‖ = ‖σ.permMatrix ℝ * (1 - J)‖ := by rw [mul_sub, mul_one, hUJ]
    _ ≤ ‖σ.permMatrix ℝ‖ * ‖(1 : Matrix n n ℝ) - J‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (Matrix.permMatrix_l2_opNorm_le σ)
      RubikConstruction.Matrix.uniform_center_norm (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

 theorem RubikConstruction.Matrix.mixed_stochastic {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (l : List (Option (Equiv.Perm n))) :
    (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod ∈ doublyStochastic ℝ n := by
  induction l with
  | nil => exact (doublyStochastic ℝ n).one_mem
  | cons t l ih =>
    change t.elim P (fun σ => σ.permMatrix ℝ) * _ ∈ _
    apply (doublyStochastic ℝ n).mul_mem _ ih
    cases t with
    | none => exact hP
    | some σ => exact permMatrix_mem_doublyStochastic

 theorem RubikConstruction.Matrix.mixed_residual_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (l : List (Option (Equiv.Perm n)))
    (hcontract : ‖P - (show Matrix n n ℝ from fun _ _ => (Fintype.card n : ℝ)⁻¹)‖ ≤ ρ) :
    ‖(l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod -
      (show Matrix n n ℝ from fun _ _ => (Fintype.card n : ℝ)⁻¹)‖ ≤ ρ ^ (l.countP Option.isNone) := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖P - J‖ ≤ ρ at hcontract
  change ‖(l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod - J‖ ≤ _
  have hPJ := RubikConstruction.Matrix.uniform_absorption P hP
  induction l with
  | nil => simpa using (RubikConstruction.Matrix.uniform_center_norm (n := n))
  | cons t l ih =>
    let Q := (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod
    have hQJ := RubikConstruction.Matrix.uniform_absorption Q (RubikConstruction.Matrix.mixed_stochastic P hP l)
    cases t with
    | none =>
      simp only [List.countP_cons]
      change ‖P * Q - J‖ ≤ ρ ^ (l.countP Option.isNone + 1)
      rw [← RubikConstruction.Matrix.residual_mul P Q J hPJ.1 hQJ.2.1 hPJ.2.2]
      calc
        ‖(P - J) * (Q - J)‖ ≤ ‖P - J‖ * ‖Q - J‖ := norm_mul_le _ _
        _ ≤ ρ * ρ ^ (l.countP Option.isNone) :=
          mul_le_mul hcontract ih (norm_nonneg _) hρ
        _ = ρ ^ (l.countP Option.isNone + 1) := by rw [pow_succ, mul_comm]
    | some σ =>
      simp only [List.countP_cons]
      change ‖σ.permMatrix ℝ * Q - J‖ ≤ ρ ^ (l.countP Option.isNone)
      have hUJ := RubikConstruction.Matrix.uniform_absorption (σ.permMatrix ℝ) permMatrix_mem_doublyStochastic
      rw [← RubikConstruction.Matrix.residual_mul (σ.permMatrix ℝ) Q J hUJ.1 hQJ.2.1 hPJ.2.2]
      calc
        ‖(σ.permMatrix ℝ - J) * (Q - J)‖ ≤ ‖σ.permMatrix ℝ - J‖ * ‖Q - J‖ := norm_mul_le _ _
        _ ≤ 1 * ρ ^ (l.countP Option.isNone) :=
          mul_le_mul (RubikConstruction.Matrix.permutation_residual_norm σ) ih (norm_nonneg _) (by norm_num)
        _ = ρ ^ (l.countP Option.isNone) := one_mul _

 theorem RubikConstruction.Matrix.mixed_entry_bound {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (l : List (Option (Equiv.Perm n)))
    (hcontract : ‖P - (show Matrix n n ℝ from fun _ _ => (Fintype.card n : ℝ)⁻¹)‖ ≤ ρ)
    (i j : n) :
    (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod i j ≤
      (Fintype.card n : ℝ)⁻¹ + ρ ^ (l.countP Option.isNone) := by
  let Q := (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  have hnorm := RubikConstruction.Matrix.mixed_residual_norm P hP ρ hρ l hcontract
  have he := RubikConstruction.Matrix.entry_norm_bound (Q - J) i j
  have habs : Q i j - (Fintype.card n : ℝ)⁻¹ ≤ ‖(Q - J) i j‖ := le_abs_self _
  change Q i j ≤ _
  linarith

 theorem RubikConstruction.Matrix.mixed_mean_zero_entry_bound {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (lam ρ : ℝ)
    (hlam : 0 ≤ lam) (hlamρ : lam ≤ ρ)
    (hcontract : ∀ x : EuclideanSpace ℝ n, (∑ i, x i) = 0 →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P x‖ ≤ lam * ‖x‖)
    (l : List (Option (Equiv.Perm n))) (i j : n) :
    (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod i j ≤
      (Fintype.card n : ℝ)⁻¹ + ρ ^ (l.countP Option.isNone) := by
  exact RubikConstruction.Matrix.mixed_entry_bound P hP ρ (hlam.trans hlamρ) l
    ((RubikConstruction.Matrix.mean_zero_residual_norm P hP lam hlam hcontract).trans hlamρ) i j

 theorem RubikConstruction.Matrix.mixed_max_bound {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (a : ℝ) (hmax : ∀ i j, P i j ≤ a)
    (l : List (Option (Equiv.Perm n))) (hl : none ∈ l) (i j : n) :
    (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod i j ≤ a := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hl
  simpa only [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
      Option.elim_none, mul_assoc] using
    RubikConstruction.Matrix.stochastic_sandwich_bound
      (s.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod P
      (t.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod a
      (RubikConstruction.Matrix.mixed_stochastic P hP s) (RubikConstruction.Matrix.mixed_stochastic P hP t) hmax i j

 theorem RubikConstruction.Matrix.permutation_average_stochastic {n c : Type*} [Fintype n] [DecidableEq n]
    [Fintype c] [Nonempty c] (σ : c → Equiv.Perm n) :
    (Fintype.card c : ℝ)⁻¹ • (∑ t, (σ t).permMatrix ℝ) ∈ doublyStochastic ℝ n := by
  have hc : (Fintype.card c : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mem_doublyStochastic_iff_sum.mpr
  constructor
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun t _ => nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic)
  constructor
  · intro i
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hr (t : c) : ∑ j, (σ t).permMatrix ℝ i j = 1 :=
      sum_row_of_mem_doublyStochastic permMatrix_mem_doublyStochastic i
    simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]
  · intro j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hc' (t : c) : ∑ i, (σ t).permMatrix ℝ i j = 1 :=
      sum_col_of_mem_doublyStochastic permMatrix_mem_doublyStochastic j
    simp only [hc', Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc]

 theorem RubikConstruction.Matrix.mixed_mean_zero_envelope {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) (lam ρ a : ℝ)
    (hlam : 0 ≤ lam) (hlamρ : lam ≤ ρ)
    (hcontract : ∀ x : EuclideanSpace ℝ n, (∑ i, x i) = 0 →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P x‖ ≤ lam * ‖x‖)
    (hmax : ∀ i j, P i j ≤ a) (l : List (Option (Equiv.Perm n)))
    (hl : none ∈ l) (i j : n) :
    (l.map (fun t => t.elim P (fun σ => σ.permMatrix ℝ))).prod i j ≤
      min a ((Fintype.card n : ℝ)⁻¹ + ρ ^ (l.countP Option.isNone)) := by
  exact le_min (RubikConstruction.Matrix.mixed_max_bound P hP a hmax l hl i j)
    (RubikConstruction.Matrix.mixed_mean_zero_entry_bound P hP lam ρ hlam hlamρ hcontract l i j)

 theorem RubikConstruction.Matrix.residual_pow {n : Type*} [Fintype n] [DecidableEq n]
    (P J : Matrix n n ℝ) (hPJ : P * J = J) (hJP : J * P = J)
    (hJJ : J * J = J) (t : ℕ) (ht : 0 < t) : (P - J) ^ t = P ^ t - J := by
  have hne : List.replicate t P ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_replicate, List.length_nil] at hlen
    omega
  have habs : ∀ A ∈ List.replicate t P, A * J = J ∧ J * A = J := by
    intro A hA
    have hAP : A = P := (List.mem_replicate.mp hA).2
    subst A
    exact ⟨hPJ, hJP⟩
  simpa using RubikConstruction.Matrix.residual_list_prod J hJJ (List.replicate t P) hne habs

open RubikJanson RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.joint_eq_expect_square {S U : Type*} [Fintype S] [Fintype U]
    (P : FiniteLaw S) (Q : FiniteLaw U) (F : S → U → ℝ) :
    (overlapLaw P Q).expect (fun ω => F ω.1 ω.2.1 * F ω.1 ω.2.2) =
      P.expect (fun s => (Q.expect (F s)) ^ 2) := by
  classical
  simp only [FiniteLaw.expect, overlapLaw, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

open RubikJanson RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.left_eq_expect {S U : Type*} [Fintype S] [Fintype U]
    (P : FiniteLaw S) (Q : FiniteLaw U) (F : S → U → ℝ) :
    (overlapLaw P Q).expect (fun ω => F ω.1 ω.2.1) =
      P.expect (fun s => Q.expect (F s)) := by
  classical
  simp only [FiniteLaw.expect, overlapLaw, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  calc
    (∑ v, P.weight s * Q.weight u * Q.weight v * F s u) =
        ∑ v, (P.weight s * Q.weight u * F s u) * Q.weight v := by
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = (P.weight s * Q.weight u * F s u) * ∑ v, Q.weight v :=
      (Finset.mul_sum _ _ _).symm
    _ = P.weight s * (Q.weight u * F s u) := by rw [Q.total]; ring

open RubikJanson RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.joint_le_bound_mul_marginal {S U : Type*} [Fintype S] [Fintype U]
    (P : FiniteLaw S) (Q : FiniteLaw U) (F : S → U → ℝ) (b : ℝ)
    (h0 : ∀ s, 0 ≤ Q.expect (F s)) (hb : ∀ s, Q.expect (F s) ≤ b) :
    (overlapLaw P Q).expect (fun ω => F ω.1 ω.2.1 * F ω.1 ω.2.2) ≤
      b * (overlapLaw P Q).expect (fun ω => F ω.1 ω.2.1) := by
  classical
  rw [joint_eq_expect_square, left_eq_expect]
  unfold FiniteLaw.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    P.weight s * (Q.expect (F s)) ^ 2 ≤
        P.weight s * (b * Q.expect (F s)) := by
      apply mul_le_mul_of_nonneg_left _ (P.nonneg s)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hb s) (h0 s)
    _ = b * (P.weight s * Q.expect (F s)) := by ring

open RubikJanson RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.uniform_indicator_moments {S U : Type*} [Fintype S] [Fintype U]
    (hS : Nonempty S) (hU : Nonempty U) (F : S → U → Prop) :
    let P := uniformLaw hS
    let Q := uniformLaw hU
    let f : S → ℝ := fun s => Q.prob (F s)
    (overlapLaw P Q).prob (fun ω => F ω.1 ω.2.1 ∧ F ω.1 ω.2.2) =
        (∑ s, f s ^ 2) / Fintype.card S ∧
      (overlapLaw P Q).prob (fun ω => F ω.1 ω.2.1) =
        (∑ s, f s) / Fintype.card S := by
  classical
  let P := uniformLaw hS
  let Q := uniformLaw hU
  let X : S → U → ℝ := fun s u => if F s u then 1 else 0
  have havg (g : S → ℝ) : P.expect g = (∑ s, g s) / Fintype.card S := by
    change (∑ s, (1 / (Fintype.card S : ℝ)) * g s) = _
    rw [← Finset.mul_sum]
    ring
  have hj : (overlapLaw P Q).prob (fun ω => F ω.1 ω.2.1 ∧ F ω.1 ω.2.2) =
      P.expect (fun s => (Q.prob (F s)) ^ 2) := by
    calc
      _ = (overlapLaw P Q).expect (fun ω => X ω.1 ω.2.1 * X ω.1 ω.2.2) := by
        unfold FiniteLaw.prob
        congr 1
        funext ω
        simp only [X]
        split_ifs <;> simp_all
      _ = _ := joint_eq_expect_square P Q X
  have hm : (overlapLaw P Q).prob (fun ω => F ω.1 ω.2.1) =
      P.expect (fun s => Q.prob (F s)) := left_eq_expect P Q X
  exact ⟨hj.trans (havg _), hm.trans (havg _)⟩

open RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.reindex_paths {L M : ℕ} {E : Type*} (a b : Fin L → Fin M)
    (W : {p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E) :
    let z := sampleEquiv a b E W
    complete a b z.1 z.2.1 = (fun i => W ⟨(i, a i), Or.inl rfl⟩) ∧
      complete a b z.1 z.2.2 = (fun i => W ⟨(i, b i), Or.inr rfl⟩) := by
  classical
  constructor
  · funext i
    dsimp [complete]
    split_ifs <;> rfl
  · funext i
    dsimp [complete]
    split_ifs with hi
    · change W ⟨(i, a i), Or.inl rfl⟩ = W ⟨(i, b i), Or.inr rfl⟩
      congr 1
      exact Subtype.ext (Prod.ext rfl hi)
    · rfl

open RubikJanson

private theorem RubikCodebook.Conditional.uniform_reindex_expect {A B : Type*} [Fintype A] [Fintype B]
    (hA : Nonempty A) (hB : Nonempty B) (e : A ≃ B) (G : B → ℝ) :
    (uniformLaw hA).expect (fun x => G (e x)) = (uniformLaw hB).expect G := by
  classical
  change (∑ x, 1 / (Fintype.card A : ℝ) * G (e x)) =
    ∑ y, 1 / (Fintype.card B : ℝ) * G y
  rw [Fintype.card_congr e]
  exact e.sum_comp (fun y => 1 / (Fintype.card B : ℝ) * G y)

open RubikJanson RubikCodebook.Conditional

private theorem RubikCodebook.Conditional.uniform_overlap_expect {S U : Type*} [Fintype S] [Fintype U]
    (hS : Nonempty S) (hU : Nonempty U) (hT : Nonempty (S × U × U))
    (G : S × U × U → ℝ) :
    (overlapLaw (uniformLaw hS) (uniformLaw hU)).expect G =
      (uniformLaw hT).expect G := by
  classical
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  simp only [overlapLaw, uniformLaw, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv_rev]
  ring

open RubikJanson RubikCodebook.Conditional
open scoped Classical

private theorem RubikCodebook.Conditional.usedBase_joint_bound {L M : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (a b : Fin L → Fin M) (H : (Fin L → E) → ℝ) (bound : ℝ)
    (h0 : ∀ s : {i : Fin L // a i = b i} → E,
      0 ≤ (uniformLaw (inferInstance : Nonempty ({i : Fin L // a i ≠ b i} → E))).expect
        (fun u => H (complete a b s u)))
    (hb : ∀ s : {i : Fin L // a i = b i} → E,
      (uniformLaw (inferInstance : Nonempty ({i : Fin L // a i ≠ b i} → E))).expect
        (fun u => H (complete a b s u)) ≤ bound) :
    (uniformLaw (inferInstance : Nonempty
      ({p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E))).expect
      (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩) *
        H (fun i => W ⟨(i, b i), Or.inr rfl⟩)) ≤
      bound * (uniformLaw (inferInstance : Nonempty
        ({p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E))).expect
        (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩)) := by
  classical
  let S := {i : Fin L // a i = b i} → E
  let U := {i : Fin L // a i ≠ b i} → E
  let V := {p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E
  let P : FiniteLaw S := uniformLaw inferInstance
  let Q : FiniteLaw U := uniformLaw inferInstance
  let R : FiniteLaw V := uniformLaw inferInstance
  let e : V ≃ S × U × U := sampleEquiv a b E
  let F : S → U → ℝ := fun s u => H (complete a b s u)
  have htransport (G : S × U × U → ℝ) :
      R.expect (fun W => G (e W)) = (overlapLaw P Q).expect G :=
    (uniform_reindex_expect inferInstance inferInstance e G).trans
      (uniform_overlap_expect inferInstance inferInstance inferInstance G).symm
  have hleft : R.expect (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩)) =
      (overlapLaw P Q).expect (fun z => F z.1 z.2.1) := by
    rw [← htransport]
    congr 1
    funext W
    exact congrArg H (reindex_paths a b W).1.symm
  have hjoint : R.expect (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩) *
      H (fun i => W ⟨(i, b i), Or.inr rfl⟩)) =
        (overlapLaw P Q).expect (fun z => F z.1 z.2.1 * F z.1 z.2.2) := by
    rw [← htransport]
    congr 1
    funext W
    exact congrArg₂ (fun x y => H x * H y)
      (reindex_paths a b W).1.symm (reindex_paths a b W).2.symm
  change R.expect _ ≤ bound * R.expect _
  rw [hjoint, hleft]
  exact joint_le_bound_mul_marginal P Q F bound h0 hb

open RubikJanson

private theorem RubikCodebook.Conditional.uniform_prod_fst_expect {A B : Type*} [Fintype A] [Fintype B]
    (hA : Nonempty A) (hB : Nonempty B) (hT : Nonempty (A × B)) (G : A → ℝ) :
    (uniformLaw hT).expect (fun x => G x.1) = (uniformLaw hA).expect G := by
  classical
  haveI := hA
  haveI := hB
  have hm : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hn : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [FiniteLaw.expect, uniformLaw, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro a _
  field_simp
  <;> ring

open RubikJanson RubikCodebook.Conditional
open scoped Classical

private theorem RubikCodebook.Conditional.uniform_restrict_expect {I E : Type*} [Fintype I] [Fintype E] [Nonempty E]
    (p : I → Prop) (G : ({i : I // p i} → E) → ℝ) :
    (uniformLaw (inferInstance : Nonempty (I → E))).expect
      (fun W => G (fun i => W i.val)) =
      (uniformLaw (inferInstance : Nonempty ({i : I // p i} → E))).expect G := by
  classical
  let A := {i : I // p i} → E
  let B := {i : I // ¬ p i} → E
  let e : (I → E) ≃ A × B := Equiv.piEquivPiSubtypeProd p (fun _ => E)
  exact (uniform_reindex_expect inferInstance inferInstance e (fun z => G z.1)).trans
    (uniform_prod_fst_expect inferInstance inferInstance inferInstance G)

open RubikJanson
open scoped Classical

private theorem RubikCodebook.Conditional.iid_uniform_expect {I E : Type*} [Fintype I] [Fintype E] [Nonempty E]
    (G : (I → E) → ℝ) :
    (productLaw (fun _ : I => uniformLaw (inferInstance : Nonempty E))).expect G =
      (uniformLaw (inferInstance : Nonempty (I → E))).expect G := by
  classical
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  simp [productLaw, uniformLaw, Fintype.card_fun, div_pow]

private theorem RubikJoint.shared_mask_random_slots {C X : Type*} (act : C → Equiv.Perm X) {k L M : ℕ}
    (a b : Fin L → Fin M) (s : {i : Fin L // a i = b i} → Fin k → C)
    (z : Fin k) :
    (RubikChannel.mixedPermutations act
      (fun i => RubikJoint.sharedMask a b s i z)).countP Option.isNone =
      L - RubikJoint.sharedCount a b := by
  classical
  rw [RubikChannel.mixedPermutations, List.ofFn_eq_map, List.countP_map]
  have hpred : (fun i : Fin L => Option.isNone
      ((RubikJoint.sharedMask a b s i z).map act)) =
      (fun i => decide (a i ≠ b i)) := by
    funext i
    by_cases h : a i = b i <;> simp [RubikJoint.sharedMask, h]
  change (List.finRange L).countP
    (fun i => Option.isNone ((RubikJoint.sharedMask a b s i z).map act)) = _
  rw [hpred]
  have hc := (List.nodup_finRange L).card_eq_countP (P := fun i => a i ≠ b i)
  calc
    _ = (Finset.univ.filter (fun i : Fin L => a i ≠ b i)).card := by
      simpa using hc.symm
    _ = Fintype.card {i : Fin L // a i ≠ b i} := (Fintype.card_subtype _).symm
    _ = L - RubikJoint.sharedCount a b := by
      rw [Fintype.card_subtype_compl]
      simp [Fintype.card_subtype, RubikJoint.sharedCount]

private theorem RubikJoint.frozen_probability_bound {C X : Type*} [Fintype C] [Nonempty C]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (act : C → Equiv.Perm X) {k L M : ℕ} (a b : Fin L → Fin M)
    (s : {i : Fin L // a i = b i} → Fin k → C) (x y : Fin k → X)
    (A ρ : ℝ) (hρ : 0 ≤ ρ) (hproper : RubikJoint.sharedCount a b < L)
    (hmax : ∀ i j, RubikChannel.transition
      (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act i j ≤ A)
    (hcontract : ∀ z : EuclideanSpace ℝ X, (∑ i, z i) = 0 →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (RubikChannel.transition
        (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act) z‖ ≤ ρ * ‖z‖) :
    (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).prob
      (fun w => RubikCodebook.eval act
        (RubikChannel.freezeArray (RubikJoint.sharedMask a b s) w) x = y) ≤
      (min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b))) ^ k := by
  classical
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty C)
  let P := RubikChannel.transition μ act
  have hP : P ∈ doublyStochastic ℝ X := RubikChannel.transition_doublyStochastic μ act
  obtain ⟨i, hi⟩ : ∃ i : Fin L, a i ≠ b i := by
    by_contra h
    have hall : ∀ i, a i = b i := fun i => by
      by_contra hn
      exact h ⟨i, hn⟩
    have hcard : RubikJoint.sharedCount a b = L := by simp [RubikJoint.sharedCount, hall]
    omega
  have hnonneg (z : Fin k) :
      0 ≤ RubikChannel.mixedMatrix μ act (fun i => RubikJoint.sharedMask a b s i z) (x z) (y z) := by
    rw [RubikChannel.mixedMatrix_worker]
    exact nonneg_of_mem_doublyStochastic
      (RubikConstruction.Matrix.mixed_stochastic P hP (RubikChannel.mixedPermutations act
        (fun i => RubikJoint.sharedMask a b s i z)))
  have hentry (z : Fin k) :
      RubikChannel.mixedMatrix μ act (fun i => RubikJoint.sharedMask a b s i z) (x z) (y z) ≤
        min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b)) := by
    let l := RubikChannel.mixedPermutations act (fun i => RubikJoint.sharedMask a b s i z)
    have hl : none ∈ l := by
      change none ∈ List.ofFn (fun i => (RubikJoint.sharedMask a b s i z).map act)
      refine List.mem_ofFn.mpr ⟨i, ?_⟩
      simp [RubikJoint.sharedMask, hi]
    have hc : l.countP Option.isNone = L - RubikJoint.sharedCount a b :=
      RubikJoint.shared_mask_random_slots act a b s z
    rw [RubikChannel.mixedMatrix_worker]
    have hm := RubikConstruction.Matrix.mixed_mean_zero_envelope P hP ρ ρ A hρ le_rfl
      hcontract hmax l hl (x z) (y z)
    simpa only [hc] using hm
  rw [RubikChannel.codebook_frozen_marginal]
  calc
    _ ≤ ∏ _z : Fin k, min A ((Fintype.card X : ℝ)⁻¹ +
        ρ ^ (L - RubikJoint.sharedCount a b)) :=
      Finset.prod_le_prod (fun z _ => hnonneg z) (fun z _ => hentry z)
    _ = _ := by simp

private theorem RubikJoint.array_uniform_expect {C : Type*} [Fintype C] [Nonempty C] (k L : ℕ)
    (H : (Fin L → Fin k → C) → ℝ) :
    (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).expect H =
      (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → Fin k → C))).expect H := by
  classical
  unfold RubikJanson.FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro W _
  simp [RubikChannel.arrayLaw, RubikJanson.uniformLaw, Fintype.card_fun, div_pow]

private theorem RubikJoint.completion_projection {C X : Type*} [Fintype C] [Nonempty C]
    (act : C → Equiv.Perm X) {k L M : ℕ} (a b : Fin L → Fin M)
    (s : {i : Fin L // a i = b i} → Fin k → C) (x y : Fin k → X) :
    (RubikJanson.uniformLaw (inferInstance : Nonempty
      ({i : Fin L // a i ≠ b i} → Fin k → C))).prob
        (fun u => RubikCodebook.eval act (RubikCodebook.Conditional.complete a b s u) x = y) =
      (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).prob
        (fun w => RubikCodebook.eval act
          (RubikChannel.freezeArray (RubikJoint.sharedMask a b s) w) x = y) := by
  classical
  let E := Fin k → C
  let U := {i : Fin L // a i ≠ b i} → E
  let S := {i : Fin L // ¬ a i ≠ b i} → E
  let Q : RubikJanson.FiniteLaw U := RubikJanson.uniformLaw inferInstance
  let R : RubikJanson.FiniteLaw (Fin L → E) := RubikJanson.uniformLaw inferInstance
  let e : (Fin L → E) ≃ U × S :=
    Equiv.piEquivPiSubtypeProd (fun i : Fin L => a i ≠ b i) (fun _ => E)
  have htransport (event : U → Prop) :
      R.prob (fun W => event (fun i => W i.val)) = Q.prob event := by
    unfold RubikJanson.FiniteLaw.prob
    exact (RubikCodebook.Conditional.uniform_reindex_expect
      (inferInstance : Nonempty (Fin L → E)) (inferInstance : Nonempty (U × S))
        e (fun z => if event z.1 then (1 : ℝ) else 0)).trans
      (RubikCodebook.Conditional.uniform_prod_fst_expect
        (inferInstance : Nonempty U) (inferInstance : Nonempty S)
        (inferInstance : Nonempty (U × S)) (fun u => if event u then (1 : ℝ) else 0))
  have harray (event : (Fin L → E) → Prop) :
      (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).prob event =
        R.prob event := by
    unfold RubikJanson.FiniteLaw.prob
    exact RubikJoint.array_uniform_expect k L _
  have hfill (W : Fin L → E) :
      RubikCodebook.Conditional.complete a b s (fun i => W i.val) =
        RubikChannel.freezeArray (RubikJoint.sharedMask a b s) W := by
    funext i z
    by_cases h : a i = b i <;>
      simp [RubikCodebook.Conditional.complete, RubikChannel.freezeArray, RubikJoint.sharedMask, h]
  calc
    _ = R.prob (fun W => RubikCodebook.eval act
        (RubikCodebook.Conditional.complete a b s (fun i => W i.val)) x = y) :=
      (htransport (fun u => RubikCodebook.eval act
        (RubikCodebook.Conditional.complete a b s u) x = y)).symm
    _ = _ := by
      rw [← harray]
      apply congrArg (RubikChannel.arrayLaw
        (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).prob
      funext W
      rw [hfill W]

private theorem RubikJoint.completion_bound {C X : Type*} [Fintype C] [Nonempty C] [Fintype X] [DecidableEq X] [Nonempty X]
(act : C → Equiv.Perm X) {k L M : ℕ} (a b : Fin L → Fin M)
(s : {i : Fin L // a i = b i} → Fin k → C) (x y : Fin k → X)
(A ρ : ℝ) (hρ : 0 ≤ ρ)
(hproper : RubikJoint.sharedCount a b < L)
(hmax : ∀ i j, RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act i j ≤ A)
(hcontract : ∀ z : EuclideanSpace ℝ X, (∑ i, z i) = 0 →
 ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act) z‖ ≤ ρ * ‖z‖) : (RubikJanson.uniformLaw (inferInstance : Nonempty ({i : Fin L // a i ≠ b i} → Fin k → C))).prob (fun u => RubikCodebook.eval act (RubikCodebook.Conditional.complete a b s u) x = y) ≤ (min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b))) ^ k  := by
  rw [RubikJoint.completion_projection]
  exact RubikJoint.frozen_probability_bound act a b s x y A ρ hρ hproper hmax hcontract

private theorem RubikJoint.dictionary_restrict_expect {C : Type*} [Fintype C] [Nonempty C] {k L M : ℕ}
    (a b : Fin L → Fin M)
    (G : ({p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → Fin k → C) → ℝ) :
    (RubikJoint.dictionaryLaw (C := C) k L M).expect
        (fun W => G (fun p => W p.val)) =
      (RubikJanson.uniformLaw (inferInstance : Nonempty
        ({p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → Fin k → C))).expect G := by
  classical
  let I := Fin L × Fin M
  let E := Fin k → C
  let p : I → Prop := fun z => z.2 = a z.1 ∨ z.2 = b z.1
  let A := {i : I // p i} → E
  let B := {i : I // ¬ p i} → E
  let e : (I → E) ≃ A × B := Equiv.piEquivPiSubtypeProd p (fun _ => E)
  exact (RubikCodebook.Conditional.uniform_reindex_expect
    (inferInstance : Nonempty (I → E)) (inferInstance : Nonempty (A × B))
      e (fun z => G z.1)).trans
    (RubikCodebook.Conditional.uniform_prod_fst_expect
      (inferInstance : Nonempty A) (inferInstance : Nonempty B)
      (inferInstance : Nonempty (A × B)) G)

private theorem RubikJoint.actual_joint_bound {C X : Type*} [Fintype C] [Nonempty C] [Fintype X] [DecidableEq X] [Nonempty X]
(act : C → Equiv.Perm X) {k L M : ℕ} (a b : Fin L → Fin M) (x y : Fin k → X)
(A ρ : ℝ) (hρ : 0 ≤ ρ) (hproper : RubikJoint.sharedCount a b < L)
(hmax : ∀ i j, RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act i j ≤ A)
(hcontract : ∀ z : EuclideanSpace ℝ X, (∑ i, z i) = 0 →
 ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act) z‖ ≤ ρ * ‖z‖) :
(RubikJoint.dictionaryLaw (C := C) k L M).prob (fun W => RubikJoint.endpointEvent act a x y W ∧ RubikJoint.endpointEvent act b x y W) ≤
(min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b))) ^ k *
(RubikJoint.dictionaryLaw (C := C) k L M).prob (RubikJoint.endpointEvent act a x y)  := by
  classical
  let E := Fin k → C
  let V := {p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = b p.1} → E
  let R : RubikJanson.FiniteLaw V := RubikJanson.uniformLaw inferInstance
  let H : (Fin L → E) → ℝ := fun w =>
    @ite ℝ (RubikCodebook.eval act w x = y) (Classical.propDecidable _) 1 0
  let B := (min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b))) ^ k
  have h0 (s : {i : Fin L // a i = b i} → E) :
      0 ≤ (RubikJanson.uniformLaw (inferInstance : Nonempty
        ({i : Fin L // a i ≠ b i} → E))).expect
          (fun u => H (RubikCodebook.Conditional.complete a b s u)) := by
    apply Finset.sum_nonneg
    intro u _
    apply mul_nonneg ((RubikJanson.uniformLaw (inferInstance : Nonempty
      ({i : Fin L // a i ≠ b i} → E))).nonneg u)
    dsimp only [H]
    split <;> norm_num
  have hb (s : {i : Fin L // a i = b i} → E) :
      (RubikJanson.uniformLaw (inferInstance : Nonempty
        ({i : Fin L // a i ≠ b i} → E))).expect
          (fun u => H (RubikCodebook.Conditional.complete a b s u)) ≤ B := by
    exact RubikJoint.completion_bound act a b s x y A ρ hρ hproper hmax hcontract
  have hleft : (RubikJoint.dictionaryLaw (C := C) k L M).prob
        (RubikJoint.endpointEvent act a x y) =
      R.expect (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩)) :=
    RubikJoint.dictionary_restrict_expect a b
      (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩))
  have hjoint : (RubikJoint.dictionaryLaw (C := C) k L M).prob
        (fun W => RubikJoint.endpointEvent act a x y W ∧ RubikJoint.endpointEvent act b x y W) =
      R.expect (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩) *
        H (fun i => W ⟨(i, b i), Or.inr rfl⟩)) := by
    calc
      _ = (RubikJoint.dictionaryLaw (C := C) k L M).expect
          (fun W => H (fun i => W (i, a i)) * H (fun i => W (i, b i))) := by
        unfold RubikJanson.FiniteLaw.prob
        apply congrArg (RubikJoint.dictionaryLaw (C := C) k L M).expect
        funext W
        dsimp only [H, RubikJoint.endpointEvent]
        by_cases ha : RubikCodebook.eval act (fun i => W (i, a i)) x = y <;>
          by_cases hb : RubikCodebook.eval act (fun i => W (i, b i)) x = y <;>
          simp [ha, hb]
      _ = _ := RubikJoint.dictionary_restrict_expect a b
        (fun W => H (fun i => W ⟨(i, a i), Or.inl rfl⟩) *
          H (fun i => W ⟨(i, b i), Or.inr rfl⟩))
  rw [hjoint, hleft]
  exact RubikCodebook.Conditional.usedBase_joint_bound a b H B h0 hb

private theorem RubikJoint.dictionary_single_path_expect {C : Type*} [Fintype C] [Nonempty C] {k L M : ℕ}
    (a : Fin L → Fin M) (H : (Fin L → Fin k → C) → ℝ) :
    (RubikJoint.dictionaryLaw (C := C) k L M).expect
        (fun W => H (fun i => W (i, a i))) =
      (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).expect H := by
  classical
  let E := Fin k → C
  let I := {p : Fin L × Fin M // p.2 = a p.1 ∨ p.2 = a p.1}
  let V := I → E
  let ei : I ≃ Fin L :=
    { toFun := fun p => p.val.1
      invFun := fun i => ⟨(i, a i), Or.inl rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl (p.property.elim id id).symm)
      right_inv := fun _ => rfl }
  let e : V ≃ (Fin L → E) := Equiv.arrowCongr ei (Equiv.refl E)
  calc
    _ = (RubikJanson.uniformLaw (inferInstance : Nonempty V)).expect
        (fun U => H (fun i => U ⟨(i, a i), Or.inl rfl⟩)) :=
      RubikJoint.dictionary_restrict_expect a a _
    _ = (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → E))).expect H :=
      RubikCodebook.Conditional.uniform_reindex_expect
        (inferInstance : Nonempty V) (inferInstance : Nonempty (Fin L → E)) e H
    _ = _ := (RubikJoint.array_uniform_expect k L H).symm

private theorem RubikJoint.dictionary_marginal {C X : Type*} [Fintype C] [Nonempty C]
    [Fintype X] [DecidableEq X] (act : C → Equiv.Perm X) {k L M : ℕ}
    (a : Fin L → Fin M) (x y : Fin k → X) :
    (RubikJoint.dictionaryLaw (C := C) k L M).prob (RubikJoint.endpointEvent act a x y) =
      ∏ z, (RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act ^ L)
        (x z) (y z) := by
  classical
  have hp (event : (Fin L → Fin k → C) → Prop) :
      (RubikJoint.dictionaryLaw (C := C) k L M).prob (fun W => event (fun i => W (i, a i))) =
        (RubikChannel.arrayLaw (RubikJanson.uniformLaw (inferInstance : Nonempty C)) k L).prob event := by
    unfold RubikJanson.FiniteLaw.prob
    exact RubikJoint.dictionary_single_path_expect (C := C) (k := k) a
      (fun w => if event w then (1 : ℝ) else 0)
  exact (hp (fun w => RubikCodebook.eval act w x = y)).trans
    (RubikChannel.codebook_marginal (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act k L x y)

private theorem RubikJoint.mean_zero_contract_of_residual {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (ρ : ℝ)
    (hresidual : ‖P - (show Matrix X X ℝ from fun _ _ => (Fintype.card X : ℝ)⁻¹)‖ ≤ ρ)
    (z : EuclideanSpace ℝ X) (hz : (∑ i, z i) = 0) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P z‖ ≤ ρ * ‖z‖ := by
  classical
  let J : Matrix X X ℝ := fun _ _ => (Fintype.card X : ℝ)⁻¹
  have hJz : Matrix.toEuclideanCLM (𝕜 := ℝ) J z = 0 := by
    ext i
    change (∑ j, (Fintype.card X : ℝ)⁻¹ * z j) = 0
    rw [← Finset.mul_sum, hz, mul_zero]
  have hrewrite : Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J) z =
      Matrix.toEuclideanCLM (𝕜 := ℝ) P z := by
    rw [map_sub]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) P z - Matrix.toEuclideanCLM (𝕜 := ℝ) J z = _
    rw [hJz, sub_zero]
  calc
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J) z‖ := congrArg norm hrewrite.symm
    _ ≤ ‖P - J‖ * ‖z‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J)).le_opNorm z
    _ ≤ ρ * ‖z‖ := mul_le_mul_of_nonneg_right hresidual (norm_nonneg z)

private theorem RubikJoint.actual_joint_bound_residual {C X : Type*} [Fintype C] [Nonempty C] [Fintype X] [DecidableEq X] [Nonempty X]
(act : C → Equiv.Perm X) {k L M : ℕ} (a b : Fin L → Fin M) (x y : Fin k → X)
(A ρ : ℝ) (hρ : 0 ≤ ρ) (hproper : RubikJoint.sharedCount a b < L)
(hmax : ∀ i j, RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act i j ≤ A)
(hresidual : ‖RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act -
 (show Matrix X X ℝ from fun _ _ => (Fintype.card X : ℝ)⁻¹)‖ ≤ ρ) :
(RubikJoint.dictionaryLaw (C := C) k L M).prob (fun W => RubikJoint.endpointEvent act a x y W ∧ RubikJoint.endpointEvent act b x y W) ≤
(min A ((Fintype.card X : ℝ)⁻¹ + ρ ^ (L - RubikJoint.sharedCount a b))) ^ k *
(RubikJoint.dictionaryLaw (C := C) k L M).prob (RubikJoint.endpointEvent act a x y)  := by
  exact RubikJoint.actual_joint_bound act a b x y A ρ hρ hproper hmax
    (fun z hz => RubikJoint.mean_zero_contract_of_residual
      (RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty C)) act)
      ρ hresidual z hz)

private theorem RubikUniversal.fixed_samples_cover {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] [Fintype State] {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (R : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hbad : ∀ x y : Fin k → State,
      (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
        (fun W => ¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y) ≤ b)
    (hsmall : (Fintype.card State : ℝ) ^ (2 * k) * b ^ R < 1) :
    ∃ B : RubikCodebook.Book Letter k L, RubikCodebook.CoversAll act B ∧
      ∀ i : Fin L, (B i).card ≤ R * M := by
  classical
  let E := (Fin k → State) × (Fin k → State)
  let Ω := RubikUniversal.Sample Letter k L M
  let bad : E → Ω → Prop := fun e W =>
    ¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) e.1 e.2
  have hE : (Fintype.card E : ℝ) = (Fintype.card State : ℝ) ^ (2 * k) := by
    simp only [E, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow]
    rw [show 2 * k = k + k by omega, pow_add]
  have hsmall' : (Fintype.card E : ℝ) * b ^ R < 1 := by rwa [hE]
  obtain ⟨trials, htrials⟩ := RubikJanson.uniform_fixed_trials_cover
    (inferInstance : Nonempty Ω) bad R b hb (fun e => hbad e.1 e.2) hsmall'
  let books : Fin R → RubikCodebook.Book Letter k L :=
    fun t => RubikUniversal.sampleBook (trials t)
  refine ⟨RubikCodebook.layerwiseUnion books, ?_, ?_⟩
  · intro x y
    apply UnionProofs.cover act books x y
    obtain ⟨t, ht⟩ := htrials (x, y)
    exact ⟨t, by simpa only [bad, not_not] using ht⟩
  · intro i
    exact UnionProofs.size books (fun t i => RubikUniversal.sampleBook_card (trials t) i) i

private theorem RubikUniversal.sample_failure_bound {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (x y : Fin k → State)
    (r m π α β : ℝ) (g : ℕ → ℝ) (hm : 0 < m)
    (hM : Real.exp ((k : ℝ) * r) / 2 ≤ (M : ℝ)) (hπ : m ^ k ≤ π)
    (hα : α = (L : ℝ) * r + Real.log m) (hαpos : 0 < α) (hβpos : 0 < β)
    (hg : ∀ s, 0 ≤ g s) (hgpos : ∀ j ∈ Finset.Ico 1 L, 0 < g (L - j))
    (hslack : ∀ j ∈ Finset.Ico 1 L,
      β ≤ (j : ℝ) * r - Real.log (g (L - j) / m))
    (hmarginal : ∀ a, RubikJanson.mean (RubikJoint.dictionaryLaw (C := Letter) k L M)
      (RubikUniversal.pathIndicator act x y) a = π)
    (hjoint : ∀ a b, (RubikAggregate.overlapGraph L M).Adj a b →
      (RubikJoint.dictionaryLaw (C := Letter) k L M).expect
        (fun W => RubikUniversal.pathIndicator act x y a W *
          RubikUniversal.pathIndicator act x y b W) ≤
            π * g (L - RubikAggregate.overlapCount a b) ^ k)
    (hpair : RubikJanson.NonedgeIndependent
      (RubikJoint.dictionaryLaw (C := Letter) k L M)
      (RubikUniversal.pathIndicator act x y) (RubikAggregate.overlapGraph L M)) :
    (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
      (fun W => ¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y) ≤
        ((2 : ℝ) ^ L + (3 : ℝ) ^ L) * Real.exp (-(k : ℝ) * min α β) := by
  let P := RubikJoint.dictionaryLaw (C := Letter) k L M
  let X := RubikUniversal.pathIndicator (L := L) (M := M) act x y
  let G := RubikAggregate.overlapGraph L M
  let ν := RubikJanson.nu P X
  let Δ := RubikJanson.Delta P X G
  have hν : ν = (M : ℝ) ^ L * π := RubikAggregate.path_nu_eq P X π hmarginal
  have hDelta := RubikAggregate.path_Delta_le P X π g k
    ((pow_pos hm k).le.trans hπ) hg hjoint
  obtain ⟨hνpos, hfirst⟩ := RubikMoments.first_moment_lower L k r m M π ν α hm hM hπ hν hα
  have hsecond := RubikMoments.delta_ratio_bound L k r m M π ν Δ β g hm hM hπ hν
    hgpos hslack hDelta
  have hF := RubikJanson.second_moment_zero P X G
    (RubikUniversal.pathIndicator_bernoulli act x y) hpair hνpos
  rw [RubikUniversal.sample_failure_eq_zeroProb]
  exact RubikMoments.second_moment_failure_bound L k ν Δ α β
    (RubikJanson.zeroProb P X) hνpos hfirst hsecond hF

open RubikJanson RubikCodebook.Conditional

private theorem RubikUniversal.pathIndicator_nonedgeIndependent {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] {k L M : ℕ}
    (act : Letter → Equiv.Perm State) (x y : Fin k → State) :
    RubikJanson.NonedgeIndependent (RubikJoint.dictionaryLaw (C := Letter) k L M)
      (RubikUniversal.pathIndicator act x y) (RubikAggregate.overlapGraph L M) := by
  classical
  intro a b hab hno
  have hd : ∀ i, b i ≠ a i := by
    intro i hi
    exact hno ⟨hab, i, hi.symm⟩
  let I := Fin L × Fin M
  let Word := Fin k → Letter
  let p : I → Prop := fun t => t.2 = a t.1
  let A := {t : I // p t} → Word
  let B := {t : I // ¬ p t} → Word
  let f : A → ℝ := fun U =>
    if RubikCodebook.eval act (fun i => U ⟨(i, a i), rfl⟩) x = y then 1 else 0
  let g : B → ℝ := fun V =>
    if RubikCodebook.eval act (fun i => V ⟨(i, b i), hd i⟩) x = y then 1 else 0
  let e : (I → Word) ≃ A × B := Equiv.piEquivPiSubtypeProd p (fun _ => Word)
  let P := RubikJoint.dictionaryLaw (C := Letter) k L M
  let PA : FiniteLaw A := uniformLaw inferInstance
  let PB : FiniteLaw B := uniformLaw inferInstance
  let PT : FiniteLaw (A × B) := uniformLaw inferInstance
  have hf (W : I → Word) : RubikUniversal.pathIndicator act x y a W = f (e W).1 := by
    simp only [RubikUniversal.pathIndicator, RubikJoint.endpointEvent, f, e,
      Equiv.piEquivPiSubtypeProd]
    split_ifs <;> simp_all
  have hg (W : I → Word) : RubikUniversal.pathIndicator act x y b W = g (e W).2 := by
    simp only [RubikUniversal.pathIndicator, RubikJoint.endpointEvent, g, e,
      Equiv.piEquivPiSubtypeProd]
    split_ifs <;> simp_all
  have htransport (H : A × B → ℝ) : P.expect (fun W => H (e W)) = PT.expect H :=
    uniform_reindex_expect inferInstance inferInstance e H
  have hprod : PT.expect (fun z => f z.1 * g z.2) = PA.expect f * PB.expect g := by
    unfold FiniteLaw.expect
    simp only [PT, PA, PB, uniformLaw, Fintype.sum_prod_type, Fintype.card_prod,
      Nat.cast_mul]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [one_div, mul_inv_rev]
    ring
  have hleft : PT.expect (fun z => f z.1) = PA.expect f :=
    uniform_prod_fst_expect inferInstance inferInstance inferInstance f
  have hright : PT.expect (fun z => g z.2) = PB.expect g := by
    have he := uniform_reindex_expect (inferInstance : Nonempty (A × B))
      (inferInstance : Nonempty (B × A)) (Equiv.prodComm A B) (fun z => g z.1)
    exact he.trans (uniform_prod_fst_expect inferInstance inferInstance inferInstance g)
  have hmeanA : RubikJanson.mean P (RubikUniversal.pathIndicator act x y) a = PA.expect f := by
    change P.expect (fun W => RubikUniversal.pathIndicator act x y a W) = _
    simp_rw [hf]
    exact (htransport _).trans hleft
  have hmeanB : RubikJanson.mean P (RubikUniversal.pathIndicator act x y) b = PB.expect g := by
    change P.expect (fun W => RubikUniversal.pathIndicator act x y b W) = _
    simp_rw [hg]
    exact (htransport _).trans hright
  change P.expect (fun W => RubikUniversal.pathIndicator act x y a W *
    RubikUniversal.pathIndicator act x y b W) = _
  simp_rw [hf, hg]
  exact (htransport _).trans (hprod.trans (congrArg₂ (fun u v : ℝ => u * v) hmeanA hmeanB).symm)

private theorem RubikUniversal.cover_from_estimates {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] [Fintype State]
    (act : Letter → Equiv.Perm State) (L : ℕ) (r m α β η : ℝ) (g : ℕ → ℝ)
    (hq : 1 < Fintype.card State) (hL : 0 < L) (hr : 0 < r) (hm : 0 < m)
    (hα : α = (L : ℝ) * r + Real.log m) (hαpos : 0 < α) (hβpos : 0 < β)
    (hη : 0 < η) (hrate : (L : ℝ) * r = Real.log (Fintype.card State) + η / 2)
    (hg : ∀ s, 0 ≤ g s) (hgpos : ∀ j ∈ Finset.Ico 1 L, 0 < g (L - j))
    (hslack : ∀ j ∈ Finset.Ico 1 L,
      β ≤ (j : ℝ) * r - Real.log (g (L - j) / m))
    (hestimates : ∀ k : ℕ, ∀ x y : Fin k → State,
      let M := ⌊Real.exp ((k : ℝ) * r)⌋₊
      ∃ π : ℝ, m ^ k ≤ π ∧
        (∀ a, RubikJanson.mean (RubikJoint.dictionaryLaw (C := Letter) k L M)
          (RubikUniversal.pathIndicator act x y) a = π) ∧
        (∀ a b, (RubikAggregate.overlapGraph L M).Adj a b →
          (RubikJoint.dictionaryLaw (C := Letter) k L M).expect
            (fun W => RubikUniversal.pathIndicator act x y a W *
              RubikUniversal.pathIndicator act x y b W) ≤
                π * g (L - RubikAggregate.overlapCount a b) ^ k)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ B : RubikCodebook.Book Letter k L,
      RubikCodebook.CoversAll act B ∧ ∀ i : Fin L, ((B i).card : ℝ) ≤
        Real.exp ((k : ℝ) * (Real.log (Fintype.card State) + η) / (L : ℝ)) := by
  let q : ℝ := Fintype.card State
  let C : ℝ := (2 : ℝ) ^ L + (3 : ℝ) ^ L
  let γ : ℝ := min α β
  have hqreal : 1 < q := by dsimp [q]; exact_mod_cast hq
  have hC : 0 < C := by dsimp [C]; positivity
  have hγ : 0 < γ := lt_min hαpos hβpos
  obtain ⟨R, hR, hRgap, K1, hK1⟩ := RubikMoments.fixed_amplification_union_tail q C γ hqreal hC hγ
  obtain ⟨K2, hK2⟩ := RubikMoments.floor_exp_half_tail r hr
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  obtain ⟨K3, hK3⟩ := RubikRates.fixed_codebook_factor_absorbed q η (R : ℝ) L hη hRreal hL
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨max K1 (max K2 K3), fun k hk => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  let M : ℕ := ⌊Real.exp ((k : ℝ) * r)⌋₊
  have hM : Real.exp ((k : ℝ) * r) / 2 ≤ (M : ℝ) := hK2 k hk2
  have hbad : ∀ x y : Fin k → State,
      (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
        (fun W => ¬ RubikCodebook.CoversPair act (RubikUniversal.sampleBook W) x y) ≤
          C * Real.exp (-(k : ℝ) * γ) := by
    intro x y
    obtain ⟨π, hπ, hmarginal, hjoint⟩ := hestimates k x y
    exact RubikUniversal.sample_failure_bound act x y r m π α β g hm hM hπ hα
      hαpos hβpos hg hgpos hslack hmarginal hjoint
      (RubikUniversal.pathIndicator_nonedgeIndependent act x y)
  obtain ⟨B, hcover, hsize⟩ := RubikUniversal.fixed_samples_cover act R
    (C * Real.exp (-(k : ℝ) * γ)) (by positivity) hbad (hK1 k hk1)
  refine ⟨B, hcover, fun i => ?_⟩
  have hnat : ((B i).card : ℝ) ≤ (R : ℝ) * (M : ℝ) := by exact_mod_cast hsize i
  have hfloor : (M : ℝ) ≤ Real.exp ((k : ℝ) * r) := Nat.floor_le (Real.exp_pos _).le
  have hkr : (k : ℝ) * r = (k : ℝ) * (Real.log q + η / 2) / (L : ℝ) := by
    change (k : ℝ) * r = (k : ℝ) * (Real.log (Fintype.card State) + η / 2) / (L : ℝ)
    rw [← hrate]
    field_simp
  calc
    ((B i).card : ℝ) ≤ (R : ℝ) * (M : ℝ) := hnat
    _ ≤ (R : ℝ) * Real.exp ((k : ℝ) * r) :=
      mul_le_mul_of_nonneg_left hfloor hRreal.le
    _ = (R : ℝ) * Real.exp ((k : ℝ) * (Real.log q + η / 2) / (L : ℝ)) := by rw [hkr]
    _ ≤ Real.exp ((k : ℝ) * (Real.log q + η) / (L : ℝ)) := hK3 k hk3

open scoped Matrix.Norms.L2Operator

private theorem RubikUniversal.residual_mean_zero_contract {State : Type*} [Fintype State]
    [DecidableEq State] (P : Matrix State State ℝ) (ρ : ℝ)
    (hnorm : ‖P - Matrix.of (fun _ _ : State => 1 / (Fintype.card State : ℝ))‖ ≤ ρ) :
    ∀ z : EuclideanSpace ℝ State, (∑ i, z i) = 0 →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P z‖ ≤ ρ * ‖z‖ := by
  intro z hz
  let J : Matrix State State ℝ := fun _ _ => 1 / (Fintype.card State : ℝ)
  have hJ : Matrix.toEuclideanCLM (𝕜 := ℝ) J z = 0 := by
    ext i
    change (∑ j, (1 / (Fintype.card State : ℝ)) * z j) = 0
    rw [← Finset.mul_sum, hz, mul_zero]
  have hvec : Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J) z =
      Matrix.toEuclideanCLM (𝕜 := ℝ) P z := by
    rw [map_sub]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) P z - Matrix.toEuclideanCLM (𝕜 := ℝ) J z = _
    rw [hJ, sub_zero]
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P z‖ =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J) z‖ := congrArg norm hvec.symm
    _ ≤ ‖P - J‖ * ‖z‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (P - J)).le_opNorm z
    _ ≤ ρ * ‖z‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg z)

private theorem RubikUniversal.power_entry_lower {State : Type*} [Fintype State]
    [DecidableEq State] [Nonempty State] (P : Matrix State State ℝ)
    (hP : P ∈ doublyStochastic ℝ State) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hnorm : ‖P - Matrix.of (fun _ _ : State => 1 / (Fintype.card State : ℝ))‖ ≤ ρ)
    (L : ℕ) (x y : State) :
    1 / (Fintype.card State : ℝ) - ρ ^ L ≤ (P ^ L) x y := by
  let J : Matrix State State ℝ := fun _ _ => (Fintype.card State : ℝ)⁻¹
  have hmix := RubikConstruction.Matrix.mixed_residual_norm P hP ρ hρ
    (List.replicate L none) (by
      convert hnorm using 1
      congr 1
      ext i j
      simp only [Matrix.sub_apply, Matrix.of_apply, one_div]
      rfl)
  have hmix' : ‖P ^ L - J‖ ≤ ρ ^ L := by
    simpa only [List.map_replicate, Option.elim_none, List.prod_replicate,
      List.countP_replicate, Option.isNone_none, if_true] using hmix
  have hentry := (RubikConstruction.Matrix.entry_norm_bound (P ^ L - J) x y).trans hmix'
  have hlow := neg_abs_le ((P ^ L - J) x y)
  change |(P ^ L) x y - (Fintype.card State : ℝ)⁻¹| ≤ ρ ^ L at hentry
  change -|(P ^ L) x y - (Fintype.card State : ℝ)⁻¹| ≤
    (P ^ L) x y - (Fintype.card State : ℝ)⁻¹ at hlow
  rw [one_div]
  linarith only [hentry, hlow]

open scoped Classical Matrix.Norms.L2Operator

private theorem RubikUniversal.norm_codebook {Letter State : Type*}
    [Fintype Letter] [Nonempty Letter] [Fintype State] [Nonempty State]
    [DecidableEq State] (act : Letter → Equiv.Perm State) (ρ a : ℝ)
    (hq : 1 < Fintype.card State) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 1 / (Fintype.card State : ℝ) ≤ a) (ha1 : a < 1)
    (hentry : ∀ x y, RubikChannel.transition
      (RubikJanson.uniformLaw (inferInstance : Nonempty Letter)) act x y ≤ a)
    (hnorm : ‖RubikChannel.transition
      (RubikJanson.uniformLaw (inferInstance : Nonempty Letter)) act -
        Matrix.of (fun _ _ : State => 1 / (Fintype.card State : ℝ))‖ ≤ ρ)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ ∃ r : ℝ, 0 < r ∧
      (L : ℝ) * r < Real.log (Fintype.card State) + η ∧
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ B : RubikCodebook.Book Letter k L,
        RubikCodebook.CoversAll act B ∧ ∀ i : Fin L,
          ((B i).card : ℝ) ≤ Real.exp ((k : ℝ) * r) := by
  classical
  let q : ℝ := Fintype.card State
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty Letter)
  let P := RubikChannel.transition μ act
  have hqreal : 1 < q := by dsimp [q]; exact_mod_cast hq
  have hq0 : 0 < q := lt_trans zero_lt_one hqreal
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨L, hL, hL4, hm, α, β, r0, hαpos, hβpos, hr0, hrate, hα, hαlo, hslack⟩ :=
    RubikRates.fixed_layer_overlap_slack q ρ a (η / 2) hqreal hρ0 hρ1 ha ha1 hη2
  let m : ℝ := 1 / q - ρ ^ L
  let g : ℕ → ℝ := fun s => min a (1 / q + ρ ^ s)
  have ha0 : 0 < a := lt_of_lt_of_le (one_div_pos.mpr hq0) ha
  have hgpos (s : ℕ) : 0 < g s :=
    lt_min ha0 (add_pos_of_pos_of_nonneg (one_div_pos.mpr hq0) (pow_nonneg hρ0.le s))
  have hP : P ∈ doublyStochastic ℝ State := RubikChannel.transition_doublyStochastic μ act
  have hresidual : ‖P - (show Matrix State State ℝ from fun _ _ =>
      (Fintype.card State : ℝ)⁻¹)‖ ≤ ρ := by
    convert hnorm using 1
    congr 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply, one_div]
    rfl
  have hcount {M : ℕ} (u v : Fin L → Fin M) :
      RubikJoint.sharedCount u v = RubikAggregate.overlapCount u v := by
    unfold RubikJoint.sharedCount RubikAggregate.overlapCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
  have hproper {M : ℕ} (u v : Fin L → Fin M)
      (huv : (RubikAggregate.overlapGraph L M).Adj u v) : RubikJoint.sharedCount u v < L := by
    have hle : RubikJoint.sharedCount u v ≤ L :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    by_contra hn
    have he : RubikJoint.sharedCount u v = L := by omega
    have he' : (Finset.univ.filter (fun i : Fin L => u i = v i)).card =
        (Finset.univ : Finset (Fin L)).card := by
      simpa only [RubikJoint.sharedCount, Finset.card_univ, Fintype.card_fin] using he
    have hall := Finset.card_filter_eq_iff.mp he'
    apply huv.1
    funext i
    exact hall i (Finset.mem_univ i)
  have hestimates : ∀ k : ℕ, ∀ x y : Fin k → State,
      let M := ⌊Real.exp ((k : ℝ) * r0)⌋₊
      ∃ π : ℝ, m ^ k ≤ π ∧
        (∀ u, RubikJanson.mean (RubikJoint.dictionaryLaw (C := Letter) k L M)
          (RubikUniversal.pathIndicator act x y) u = π) ∧
        (∀ u v, (RubikAggregate.overlapGraph L M).Adj u v →
          (RubikJoint.dictionaryLaw (C := Letter) k L M).expect
            (fun W => RubikUniversal.pathIndicator act x y u W *
              RubikUniversal.pathIndicator act x y v W) ≤
                π * g (L - RubikAggregate.overlapCount u v) ^ k) := by
    intro k x y
    let M := ⌊Real.exp ((k : ℝ) * r0)⌋₊
    let π : ℝ := ∏ z : Fin k, (P ^ L) (x z) (y z)
    have hπ : m ^ k ≤ π := by
      have hp : (∏ _z : Fin k, m) ≤ ∏ z : Fin k, (P ^ L) (x z) (y z) := by
        apply Finset.prod_le_prod
        · intro z _; exact hm.le
        · intro z _
          exact RubikUniversal.power_entry_lower P hP ρ hρ0.le hnorm L (x z) (y z)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp
    have hmarginal (u : Fin L → Fin M) :
        RubikJanson.mean (RubikJoint.dictionaryLaw (C := Letter) k L M)
          (RubikUniversal.pathIndicator act x y) u = π := by
      change (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
        (RubikJoint.endpointEvent act u x y) = π
      exact RubikJoint.dictionary_marginal act u x y
    refine ⟨π, hπ, hmarginal, ?_⟩
    intro u v huv
    have hj := RubikJoint.actual_joint_bound_residual act u v x y a ρ hρ0.le
      (hproper u v huv) hentry hresidual
    have hboth : (RubikJoint.dictionaryLaw (C := Letter) k L M).expect
        (fun W => RubikUniversal.pathIndicator act x y u W *
          RubikUniversal.pathIndicator act x y v W) =
      (RubikJoint.dictionaryLaw (C := Letter) k L M).prob
        (fun W => RubikJoint.endpointEvent act u x y W ∧
          RubikJoint.endpointEvent act v x y W) := by
      unfold RubikJanson.FiniteLaw.prob
      congr 1
      funext W
      dsimp only [RubikUniversal.pathIndicator]
      split_ifs <;> simp_all
    rw [hboth]
    rw [RubikJoint.dictionary_marginal act u x y, hcount] at hj
    simpa only [g, one_div, mul_comm] using hj
  obtain ⟨K, hK⟩ := RubikUniversal.cover_from_estimates act L r0 m α β (η / 2) g
    hq hL hr0 hm hα hαpos hβpos hη2 hrate (fun s => (hgpos s).le)
    (fun j _ => hgpos (L - j))
    (fun j hj => hslack j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2) hestimates
  let r : ℝ := (Real.log q + η / 2) / (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : 0 < r := div_pos (add_pos (Real.log_pos hqreal) hη2) hLreal
  have hLr : (L : ℝ) * r = Real.log q + η / 2 := by dsimp [r]; field_simp
  refine ⟨L, hL, hL4, r, hr, ?_, K, fun k hk => ?_⟩
  · change (L : ℝ) * r < Real.log q + η
    rw [hLr]
    linarith only [hη]
  · obtain ⟨B, hcover, hsize⟩ := hK k hk
    refine ⟨B, hcover, fun i => ?_⟩
    simpa only [r, mul_div_assoc] using hsize i

private theorem RubikChannel.orientedQuotient {V : Type*} [DecidableEq V] (u v w a b : V) (h : [u,v,w,a,b].Nodup) :
  ([v,a,b,w].formPerm)⁻¹ * [u,a,b,w].formPerm = [u,v,w].formPerm := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at h
  ext x
  simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one,
    mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
  simp only [Equiv.swap_apply_def]
  grind

open Equiv.Perm

set_option maxHeartbeats 600000

private theorem explicitKernels {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 9 ≤ Fintype.card V) (u v w : V) (ht : [u,v,w].Nodup) :
    ([u,v,w].formPerm,1) ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) ∧
    (1,[u,v,w].formPerm) ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) := by
  have hcard : Fintype.card (Fin 6) ≤ (Finset.univ \ ({u,v,w} : Finset V)).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hc : ({u,v,w} : Finset V).card = 3 := by
      simpa using List.toFinset_card_of_nodup ht
    rw [hc]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hcard
  have hfresh (i : Fin 6) : e i ≠ u ∧ e i ≠ v ∧ e i ≠ w := by
    have hi := (Finset.mem_sdiff.mp (he (Set.mem_range_self i))).2
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi
  have hinj (i j : Fin 6) : e i = e j ↔ i = j := e.injective.eq_iff
  have hfive : [u,v,w,e 0,e 1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at ht ⊢
    have := hfresh 0
    have := hfresh 1
    have := (hinj 0 1).not.mpr (by decide)
    tauto
  have hnA : [u,e 0,e 1,w].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hfive ⊢
    tauto
  have hnA' : [v,e 0,e 1,w].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true] at hfive ⊢
    tauto
  have hnB : [e 2,e 3,e 4,e 5].Nodup := by
    simp [List.nodup_cons, hinj]
  have four (l : List V) (hn : l.Nodup) (hl : l.length = 4) :
      l.formPerm.IsCycle ∧ l.formPerm.support.card = 4 := by
    refine ⟨List.isCycle_formPerm hn (by omega), ?_⟩
    rw [List.support_formPerm_of_nodup l hn (by intro x hx; subst l; simp at hl)]
    rw [List.toFinset_card_of_nodup hn, hl]
  have hsA := List.support_formPerm_of_nodup [u,e 0,e 1,w] hnA (by simp)
  have hsA' := List.support_formPerm_of_nodup [v,e 0,e 1,w] hnA' (by simp)
  have hsB := List.support_formPerm_of_nodup [e 2,e 3,e 4,e 5] hnB (by simp)
  have hdA : Disjoint ([u,e 0,e 1,w].formPerm.support) ([e 2,e 3,e 4,e 5].formPerm.support) := by
    rw [hsA, hsB]
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
      Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    have := hfresh 2
    have := hfresh 3
    have := hfresh 4
    have := hfresh 5
    simp_all only [hinj]
    tauto
  have hdA' : Disjoint ([v,e 0,e 1,w].formPerm.support) ([e 2,e 3,e 4,e 5].formPerm.support) := by
    rw [hsA', hsB]
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
      Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    have := hfresh 2
    have := hfresh 3
    have := hfresh 4
    have := hfresh 5
    simp_all only [hinj]
    tauto
  have hAB : ([u,e 0,e 1,w].formPerm,[e 2,e 3,e 4,e 5].formPerm) ∈
      RubikChannel.disjointFourCycleAlphabet V :=
    ⟨four _ hnA rfl, four _ hnB rfl, hdA⟩
  have hA'B : ([v,e 0,e 1,w].formPerm,[e 2,e 3,e 4,e 5].formPerm) ∈
      RubikChannel.disjointFourCycleAlphabet V :=
    ⟨four _ hnA' rfl, four _ hnB rfl, hdA'⟩
  have hBA : ([e 2,e 3,e 4,e 5].formPerm,[u,e 0,e 1,w].formPerm) ∈
      RubikChannel.disjointFourCycleAlphabet V :=
    ⟨four _ hnB rfl, four _ hnA rfl, hdA.symm⟩
  have hBA' : ([e 2,e 3,e 4,e 5].formPerm,[v,e 0,e 1,w].formPerm) ∈
      RubikChannel.disjointFourCycleAlphabet V :=
    ⟨four _ hnB rfl, four _ hnA' rfl, hdA'.symm⟩
  have hq := RubikChannel.orientedQuotient u v w (e 0) (e 1) hfive
  constructor
  · have hm := (Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V)).mul_mem
      ((Subgroup.closure _).inv_mem (Subgroup.subset_closure hA'B)) (Subgroup.subset_closure hAB)
    simpa only [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel, hq] using hm
  · have hm := (Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V)).mul_mem
      ((Subgroup.closure _).inv_mem (Subgroup.subset_closure hBA')) (Subgroup.subset_closure hBA)
    simpa only [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel, hq] using hm

private theorem RubikChannel.threeCycleKernels (V : Type*) [Fintype V] [DecidableEq V] (hV : 9 ≤ Fintype.card V)
    (p : Equiv.Perm V) (hp : p.IsThreeCycle) :
    (p,1) ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) ∧
    (1,p) ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hp.card_support]; decide : 0 < p.support.card)
  have hrep := hp.eq_swap_mul_swap_iff_mem_support.mpr hu
  have hn := hp.nodup_iff_mem_support.mpr hu
  have hk := explicitKernels hV u (p u) (p (p u)) hn
  simpa only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, ← hrep] using hk

open Equiv.Perm

set_option maxHeartbeats 600000

private theorem alphabet_nonempty (V : Type*) [Fintype V] [DecidableEq V]
    (hV : 8 ≤ Fintype.card V) : (RubikChannel.disjointFourCycleAlphabet V).Nonempty := by
  have hc : Fintype.card (Fin 8) ≤ (Finset.univ : Finset V).card := by simpa using hV
  obtain ⟨e, _⟩ := Function.Embedding.exists_of_card_le_finset hc
  have hinj (i j : Fin 8) : e i = e j ↔ i = j := e.injective.eq_iff
  have hnA : [e 0,e 1,e 2,e 3].Nodup := by simp [List.nodup_cons, hinj]
  have hnB : [e 4,e 5,e 6,e 7].Nodup := by simp [List.nodup_cons, hinj]
  have hsA := List.support_formPerm_of_nodup [e 0,e 1,e 2,e 3] hnA (by simp)
  have hsB := List.support_formPerm_of_nodup [e 4,e 5,e 6,e 7] hnB (by simp)
  refine ⟨([e 0,e 1,e 2,e 3].formPerm,[e 4,e 5,e 6,e 7].formPerm), ?_⟩
  refine ⟨⟨List.isCycle_formPerm hnA (by simp), ?_⟩,
    ⟨List.isCycle_formPerm hnB (by simp), ?_⟩, ?_⟩
  · rw [hsA, List.toFinset_card_of_nodup hnA]
    rfl
  · rw [hsB, List.toFinset_card_of_nodup hnB]
    rfl
  · rw [hsA, hsB]
    simp [Finset.disjoint_left, hinj]

private theorem RubikChannel.generated_eq_equalParity_set (V : Type*) [Fintype V] [DecidableEq V] (hV : 9 ≤ Fintype.card V) :
  (Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) : Set (Equiv.Perm V × Equiv.Perm V)) =
    {g | Equiv.Perm.sign g.1 = Equiv.Perm.sign g.2} := by
  let K := Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V)
  have hs (g : Equiv.Perm V × Equiv.Perm V)
      (hg : g ∈ RubikChannel.disjointFourCycleAlphabet V) :
      sign g.1 = -1 ∧ sign g.2 = -1 := by
    exact ⟨by rw [hg.1.1.sign, hg.1.2]; norm_num,
      by rw [hg.2.1.1.sign, hg.2.1.2]; norm_num⟩
  have parity : ∀ g ∈ K, sign g.1 = sign g.2 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact (hs g hg).1.trans (hs g hg).2.symm
    | one => simp
    | mul g h hg hh hgp hhp => simpa only [Prod.fst_mul, Prod.snd_mul, map_mul, hgp, hhp]
    | inv g hg hgp => simpa only [Prod.fst_inv, Prod.snd_inv, map_inv, hgp]
  have evenK (p : Equiv.Perm V) (hp : sign p = 1) : (p,1) ∈ K ∧ (1,p) ∈ K := by
    have hpA : p ∈ Subgroup.closure {p : Equiv.Perm V | p.IsThreeCycle} := by
      simpa only [closure_three_cycles_eq_alternating, mem_alternatingGroup] using hp
    clear hp
    induction hpA using Subgroup.closure_induction with
    | mem p hp => exact RubikChannel.threeCycleKernels V hV p hp
    | one => exact ⟨K.one_mem, K.one_mem⟩
    | mul p q hp hq ihp ihq =>
      exact ⟨by simpa using K.mul_mem ihp.1 ihq.1, by simpa using K.mul_mem ihp.2 ihq.2⟩
    | inv p hp ih =>
      exact ⟨by simpa using K.inv_mem ih.1, by simpa using K.inv_mem ih.2⟩
  have evenPair (p q : Equiv.Perm V) (hp : sign p = 1) (hq : sign q = 1) : (p,q) ∈ K := by
    simpa using K.mul_mem (evenK p hp).1 (evenK q hq).2
  apply Set.ext
  rintro ⟨p,q⟩
  constructor
  · exact parity (p,q)
  · intro hpq
    change sign p = sign q at hpq
    rcases Int.units_eq_one_or (sign p) with hp | hp
    · exact evenPair p q hp (hpq ▸ hp)
    · obtain ⟨g,hg⟩ := alphabet_nonempty V (by omega)
      obtain ⟨hg1,hg2⟩ := hs g hg
      have hq : sign q = -1 := hpq ▸ hp
      have hr := evenPair (p * g.1⁻¹) (q * g.2⁻¹)
        (by simp [hp, hg1]) (by simp [hq, hg2])
      have hm := K.mul_mem hr (Subgroup.subset_closure hg)
      have heq : (p * g.1⁻¹,q * g.2⁻¹) * g = (p,q) := by
        apply Prod.ext <;> simp
      rw [heq] at hm
      exact hm

private theorem RubikChannel.generated_eq_equalParity_fin24 :
  Subgroup.closure (RubikChannel.disjointFourCycleAlphabet (Fin 24)) =
    RubikChannel.equalParitySubgroup (Fin 24) := by
  apply SetLike.coe_injective
  exact RubikChannel.generated_eq_equalParity_set (Fin 24) (by decide)

open Equiv.Perm

private theorem RubikChannel.Colour.alternating_transitive {V Colour : Type*} [Fintype V] [DecidableEq V] (κ : V → Colour)
    (ρ : Equiv.Perm V) (hρ : sign ρ = -1) (hκ : κ ∘ ρ = κ)
    (x y : RubikChannel.Colour.Orbit κ) :
    ∃ σ ∈ alternatingGroup V, RubikChannel.Colour.orbitAction κ σ x = y := by
  have evenRep (f : RubikChannel.Colour.Orbit κ) :
      ∃ σ ∈ alternatingGroup V, f.val = κ ∘ σ := by
    obtain ⟨σ, hσ⟩ := f.property
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, mem_alternatingGroup.mpr hs, hσ⟩
    · refine ⟨ρ * σ, mem_alternatingGroup.mpr (by simp [hρ, hs]), ?_⟩
      rw [hσ]
      funext i
      exact (congrFun hκ (σ i)).symm
  obtain ⟨σ, hσ, hx⟩ := evenRep x
  obtain ⟨τ, hτ, hy⟩ := evenRep y
  refine ⟨τ⁻¹ * σ, (alternatingGroup V).mul_mem ((alternatingGroup V).inv_mem hτ) hσ, ?_⟩
  apply Subtype.ext
  funext i
  change x.val ((τ⁻¹ * σ)⁻¹ i) = y.val i
  rw [hx, hy]
  simp [Function.comp_def]

open Equiv.Perm

private theorem RubikChannel.Colour.pair_transitive {V Colour : Type*} [Fintype V] [DecidableEq V]
    (hV : 9 ≤ Fintype.card V) (κ : V → Colour) (ρ : Equiv.Perm V)
    (hρ : sign ρ = -1) (hκ : κ ∘ ρ = κ)
    (x y : RubikChannel.Colour.Orbit κ × RubikChannel.Colour.Orbit κ) :
    (∃ g ∈ RubikChannel.equalParitySubgroup V,
      RubikChannel.Colour.pairAction κ g x = y) ∧
    (∃ g ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V),
      RubikChannel.Colour.pairAction κ g x = y) := by
  obtain ⟨σ, hσ, h₁⟩ := RubikChannel.Colour.alternating_transitive κ ρ hρ hκ x.1 y.1
  obtain ⟨τ, hτ, h₂⟩ := RubikChannel.Colour.alternating_transitive κ ρ hρ hκ x.2 y.2
  have heq : RubikChannel.Colour.pairAction κ (σ,τ) x = y := by
    apply Prod.ext
    · exact h₁
    · exact h₂
  have hsign : sign σ = sign τ := by
    rw [mem_alternatingGroup.mp hσ, mem_alternatingGroup.mp hτ]
  have hH : (σ,τ) ∈ RubikChannel.equalParitySubgroup V := hsign
  have hC : (σ,τ) ∈ Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) := by
    change (σ,τ) ∈ (Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V) :
      Set (Equiv.Perm V × Equiv.Perm V))
    rw [show ((Subgroup.closure (RubikChannel.disjointFourCycleAlphabet V)) :
        Set (Equiv.Perm V × Equiv.Perm V)) =
        {g | sign g.1 = sign g.2} from RubikChannel.generated_eq_equalParity_set V hV]
    exact hsign
  exact ⟨⟨(σ,τ), hH, heq⟩, ⟨(σ,τ), hC, heq⟩⟩

private theorem RubikChannel.alphabet_symmetric_nonempty (V : Type*) [Fintype V] [DecidableEq V] (hV : 8 ≤ Fintype.card V) :
    (∀ g ∈ RubikChannel.disjointFourCycleAlphabet V,
      g⁻¹ ∈ RubikChannel.disjointFourCycleAlphabet V) ∧
    (RubikChannel.disjointFourCycleAlphabet V).Nonempty := by
  constructor
  · intro g hg
    exact ⟨⟨hg.1.1.inv, by simpa using hg.1.2⟩,
      ⟨hg.2.1.1.inv, by simpa using hg.2.1.2⟩, by simpa using hg.2.2⟩
  · exact alphabet_nonempty V hV

open Equiv.Perm

private theorem RubikChannel.Colour.normalTable_selfloop :
  let κ := RubikGeometry.normalTable
  let s : RubikChannel.Colour.Orbit κ := ⟨κ, ⟨1, rfl⟩⟩
  let g : Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24) :=
    ([0,1,2,3].formPerm, [20,21,22,23].formPerm)
  sign (Equiv.swap (0 : Fin 24) 1) = -1 ∧
  κ ∘ Equiv.swap (0 : Fin 24) 1 = κ ∧
  g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) ∧
  RubikChannel.Colour.pairAction κ g (s,s) = (s,s) := by
  dsimp only
  have hA : ([0,1,2,3] : List (Fin 24)).Nodup := by decide
  have hB : ([20,21,22,23] : List (Fin 24)).Nodup := by decide
  have hsA := List.support_formPerm_of_nodup [0,1,2,3] hA (by simp)
  have hsB := List.support_formPerm_of_nodup [20,21,22,23] hB (by simp)
  refine ⟨sign_swap (by decide), ?_, ?_, ?_⟩
  · decide
  · refine ⟨⟨List.isCycle_formPerm hA (by decide), ?_⟩,
      ⟨List.isCycle_formPerm hB (by decide), ?_⟩, ?_⟩
    · rw [hsA, List.toFinset_card_of_nodup hA]; rfl
    · rw [hsB, List.toFinset_card_of_nodup hB]; rfl
    · rw [hsA, hsB]
      decide
  · apply Prod.ext <;> apply Subtype.ext <;> decide

noncomputable section
open scoped BigOperators Classical

open RubikChannel.Paired

private def inverseLetter : Letter ≃ Letter where
  toFun c := ⟨c.val⁻¹, ⟨⟨c.property.1.1.inv, by simpa using c.property.1.2⟩,
    ⟨c.property.2.1.1.inv, by simpa using c.property.2.1.2⟩,
    by simpa using c.property.2.2⟩⟩
  invFun c := ⟨c.val⁻¹, ⟨⟨c.property.1.1.inv, by simpa using c.property.1.2⟩,
    ⟨c.property.2.1.1.inv, by simpa using c.property.2.1.2⟩,
    by simpa using c.property.2.2⟩⟩
  left_inv c := by apply Subtype.ext; exact inv_inv c.val
  right_inv c := by apply Subtype.ext; exact inv_inv c.val

private theorem uniform_weight_pos (c : Letter) : 0 < μ.weight c := by
  change 0 < 1 / (Fintype.card Letter : ℝ)
  positivity

private theorem inverse_act (c : Letter) : act (inverseLetter c) = (act c)⁻¹ := by
  change RubikChannel.Colour.pairAction Seed c.val⁻¹ =
    (RubikChannel.Colour.pairAction Seed c.val)⁻¹
  exact map_inv _ _

private theorem transition_stochastic {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) :
    RubikChannel.transition μ act ∈ doublyStochastic ℝ X := by
  classical
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (μ.nonneg c)
    simp only [RubikChannel.rowPermutation]
    split <;> norm_num
  · intro x
    change (∑ y, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, eq_comm] using μ.total
  · intro y
    change (∑ x, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, Equiv.apply_eq_iff_eq_symm_apply] using μ.total

private theorem RubikChannel.Paired.stochastic_symmetric :
    (∀ x y, 0 ≤ P x y) ∧ P ∈ doublyStochastic ℝ State ∧ P.IsSymm := by
  have hds : P ∈ doublyStochastic ℝ State := transition_stochastic μ act
  refine ⟨(mem_doublyStochastic_iff_sum.mp hds).1, hds, ?_⟩
  apply Matrix.IsSymm.ext
  intro x y
  change (∑ c, μ.weight c * RubikChannel.rowPermutation (act c) y x) =
    ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y
  apply Fintype.sum_equiv inverseLetter
  intro c
  rw [inverse_act]
  have hw : μ.weight c = μ.weight (inverseLetter c) := rfl
  rw [hw]
  congr 1
  simp only [RubikChannel.rowPermutation]
  have he : act c y = x ↔ (act c)⁻¹ x = y := by
    exact ⟨fun h => by rw [← h]; simp, fun h => by rw [← h]; simp⟩
  simp only [he]

private theorem RubikChannel.closure_word {G : Type*} [Group G] (S : Set G)
    (hInv : ∀ g ∈ S, g⁻¹ ∈ S) {g : G} (hg : g ∈ Subgroup.closure S) :
    ∃ l : List G, (∀ a ∈ l, a ∈ S) ∧ l.prod = g := by
  induction hg using Subgroup.closure_induction'' with
  | mem a ha => exact ⟨[a], by simpa, by simp⟩
  | inv_mem a ha => exact ⟨[a⁻¹], by simpa using hInv a ha, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨la, hla, ha'⟩ := iha
    obtain ⟨lb, hlb, hb'⟩ := ihb
    refine ⟨la ++ lb, ?_, by simp [List.prod_append, ha', hb']⟩
    intro x hx
    exact (List.mem_append.mp hx).elim (hla x) (hlb x)

noncomputable section
open scoped BigOperators

 theorem RubikAsymptotics.Primitive.pow_add_entry_pos {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y)
    {a b : ℕ} {x z y : X}
    (ha : 0 < (P ^ a) x z) (hb : 0 < (P ^ b) z y) :
    0 < (P ^ (a + b)) x y := by
  rw [pow_add, Matrix.mul_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun w _ =>
    mul_nonneg (Matrix.pow_apply_nonneg hP a x w) (Matrix.pow_apply_nonneg hP b w y))).mpr
      ⟨z, Finset.mem_univ z, mul_pos ha hb⟩

 theorem RubikAsymptotics.Primitive.selfloop_power_pos {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y)
    {z : X} (hz : 0 < P z z) (k : ℕ) : 0 < (P ^ k) z z := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact RubikAsymptotics.Primitive.pow_add_entry_pos P hP ih (by simpa using hz : 0 < (P ^ 1) z z)

 theorem RubikAsymptotics.Primitive.positive_power_of_irreducible_selfloop {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hP : ∀ x y, 0 ≤ P x y)
    (hirr : ∀ x y, ∃ k : ℕ, 0 < (P ^ k) x y)
    (hloop : ∃ z, 0 < P z z) :
    ∃ K : ℕ, 0 < K ∧ ∀ x y, 0 < (P ^ K) x y := by
  classical
  obtain ⟨z, hz⟩ := hloop
  choose a ha using (fun x : X => hirr x z)
  choose b hb using (fun y : X => hirr z y)
  let bound : ℕ := Finset.univ.sup (fun xy : X × X => a xy.1 + b xy.2)
  refine ⟨bound + 1, Nat.succ_pos _, ?_⟩
  intro x y
  have hbound : a x + b y ≤ bound := Finset.le_sup (f := fun xy : X × X => a xy.1 + b xy.2)
    (Finset.mem_univ (x, y))
  let padding : ℕ := bound + 1 - (a x + b y)
  have hpad := RubikAsymptotics.Primitive.selfloop_power_pos P hP hz padding
  have hroute := RubikAsymptotics.Primitive.pow_add_entry_pos P hP (RubikAsymptotics.Primitive.pow_add_entry_pos P hP (ha x) hpad) (hb y)
  have hlen : a x + padding + b y = bound + 1 := by dsimp [padding]; omega
  rwa [hlen] at hroute

 theorem RubikAsymptotics.Primitive.list_path_power_pos {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (x : X) (l : List X)
    (hpath : (x :: l).IsChain (fun i j => 0 < P i j)) :
    0 < (P ^ l.length) x ((x :: l).getLast (List.cons_ne_nil x l)) := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
    have hfirst : 0 < (P ^ 1) x y := by
      simpa using (List.isChain_cons_cons.mp hpath).1
    have htail := ih y (List.isChain_cons_cons.mp hpath).2
    have hcomp := RubikAsymptotics.Primitive.pow_add_entry_pos P hP hfirst htail
    simpa [Nat.add_comm] using hcomp

open RubikChannel.Paired

private theorem actual_nonneg : ∀ x y, 0 ≤ P x y :=
  RubikChannel.Paired.stochastic_symmetric.1

private theorem letter_edge (c : Letter) (x : State) : 0 < P x (act c x) := by
  change 0 < ∑ d, μ.weight d * RubikChannel.rowPermutation (act d) x (act c x)
  apply (Finset.sum_pos_iff_of_nonneg (fun d _ =>
    mul_nonneg (μ.nonneg d) (by simp [RubikChannel.rowPermutation]; split <;> norm_num))).mpr
  refine ⟨c, Finset.mem_univ c, ?_⟩
  have hc : RubikChannel.rowPermutation (act c) x (act c x) = 1 := by
    simp [RubikChannel.rowPermutation]
  rw [hc,mul_one]
  change 0 < 1 / (Fintype.card Letter : ℝ)
  positivity

private theorem word_positive (l : List (Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24)))
    (hl : ∀ g ∈ l, g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)) (x : State) :
    0 < (P ^ l.length) x (RubikChannel.Colour.pairAction Seed l.prod x) := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have hg : g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) := hl g (by simp)
    have htail : ∀ a ∈ l, a ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) :=
      fun a ha => hl a (List.mem_cons_of_mem _ ha)
    have h₁ := ih htail
    have h₂ : 0 < (P ^ 1) (RubikChannel.Colour.pairAction Seed l.prod x)
        (RubikChannel.Colour.pairAction Seed g (RubikChannel.Colour.pairAction Seed l.prod x)) := by
      simpa only [pow_one, act] using letter_edge (⟨g,hg⟩ : Letter)
        (RubikChannel.Colour.pairAction Seed l.prod x)
    have hprod := RubikAsymptotics.Primitive.pow_add_entry_pos P actual_nonneg h₁ h₂
    simpa only [List.length_cons, List.prod_cons, map_mul, Equiv.Perm.mul_apply] using hprod

private theorem actual_irreducible (x y : State) : ∃ k : ℕ, 0 < (P ^ k) x y := by
  have hstab := RubikChannel.Colour.normalTable_selfloop
  obtain ⟨_,hκ,_,_⟩ := hstab
  have hρ : Equiv.Perm.sign (Equiv.swap (0 : Fin 24) 1) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  obtain ⟨g,hg,hxy⟩ := (RubikChannel.Colour.pair_transitive (by decide) Seed
    (Equiv.swap (0 : Fin 24) 1) hρ hκ x y).2
  have hInv : ∀ g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24),
      g⁻¹ ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) := by
    intro a ha
    exact ⟨⟨ha.1.1.inv, by simpa using ha.1.2⟩,
      ⟨ha.2.1.1.inv, by simpa using ha.2.1.2⟩, by simpa using ha.2.2⟩
  obtain ⟨l,hl,heq⟩ := RubikChannel.closure_word _ hInv hg
  refine ⟨l.length, ?_⟩
  have hp := word_positive l hl x
  rwa [heq,hxy] at hp

private theorem actual_seed_loop : 0 < P seedState seedState := by
  have hfix : act loopLetter seedState = seedState := by
    exact RubikChannel.Colour.normalTable_selfloop.2.2.2
  simpa only [hfix] using letter_edge loopLetter seedState

private theorem RubikChannel.Paired.irreducible_selfloop :
    (∀ x y, ∃ k : ℕ, 0 < (P ^ k) x y) ∧ 0 < P seedState seedState :=
  ⟨actual_irreducible, actual_seed_loop⟩

open RubikChannel.Paired

private theorem RubikChannel.Paired.primitive :
    P ∈ doublyStochastic ℝ State ∧ P.IsSymm ∧
    ∃ K : ℕ, 0 < K ∧ ∀ x y, 0 < (P ^ K) x y := by
  obtain ⟨hn, hd, hs⟩ := RubikChannel.Paired.stochastic_symmetric
  obtain ⟨hi, hl⟩ := RubikChannel.Paired.irreducible_selfloop
  exact ⟨hd, hs, RubikAsymptotics.Primitive.positive_power_of_irreducible_selfloop P hn hi ⟨seedState,hl⟩⟩

noncomputable section
open scoped Matrix.Norms.L2Operator BigOperators

private theorem RubikAsymptotics.Spectral.stochastic_residual_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖P - J‖ ≤ 1 := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖P - J‖ ≤ 1
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hPJ : P * J = J := by
    ext i j
    change (∑ k, P i k * (Fintype.card n : ℝ)⁻¹) = _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]
  have hJJ : J * J = J := by
    ext i j
    change (∑ _ : n, (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹) = (Fintype.card n : ℝ)⁻¹
    simp [hc]
  have hstar : star J = J := by
    ext i j
    change star (J j i) = J i j
    simp [J]
  have hproj : IsStarProjection J := ⟨hJJ, hstar⟩
  have hres : P - J = P * (1 - J) := by rw [mul_sub, mul_one, hPJ]
  rw [hres]
  calc
    ‖P * (1 - J)‖ ≤ ‖P‖ * ‖1 - J‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (Matrix.l2_opNorm_le_one_of_mem_doublyStochastic hP)
      (IsStarProjection.norm_le _ hproj.one_sub) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

private theorem RubikAsymptotics.Spectral.positive_stochastic_gap {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (hp : ∀ i j, 0 < P i j) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖P - J‖ < 1 := by
  classical
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖P - J‖ < 1
  have hc : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  let a : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun ij : n × n => P ij.1 ij.2)
  have ha : 0 < a := by
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun ij _ => hp ij.1 ij.2)
  have haP (i j : n) : a ≤ P i j := Finset.inf'_le _ (Finset.mem_univ (i,j))
  let ε : ℝ := min (1 / 2) ((Fintype.card n : ℝ) * a)
  have he : 0 < ε := lt_min (by norm_num) (mul_pos hc ha)
  have he1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hd : 0 < 1 - ε := sub_pos.mpr he1
  have hminor (i j : n) : ε * J i j ≤ P i j := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1/2 : ℝ) ((Fintype.card n : ℝ) * a))
      (inv_nonneg.mpr hc.le)
    have heJa : ε * J i j ≤ a := by
      simpa [ε, J, mul_assoc, mul_comm, mul_left_comm, hc.ne'] using h
    exact heJa.trans (haP i j)
  let R : Matrix n n ℝ := (1 - ε)⁻¹ • (P - ε • J)
  have hR : R ∈ doublyStochastic ℝ n := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      change 0 ≤ (1 - ε)⁻¹ * (P i j - ε * J i j)
      exact mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr (hminor i j))
    · intro i
      change (∑ j, (1 - ε)⁻¹ * (P i j - ε * J i j)) = 1
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_row_of_mem_doublyStochastic hP]
      have hsum : ∑ j, J i j = 1 := by simp [J, hc.ne']
      rw [hsum, mul_one, inv_mul_cancel₀ hd.ne']
    · intro j
      change (∑ i, (1 - ε)⁻¹ * (P i j - ε * J i j)) = 1
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_col_of_mem_doublyStochastic hP]
      have hsum : ∑ i, J i j = 1 := by simp [J, hc.ne']
      rw [hsum, mul_one, inv_mul_cancel₀ hd.ne']
  have hdecomp : P - J = (1 - ε) • (R - J) := by
    ext i j
    change P i j - J i j = (1 - ε) * ((1 - ε)⁻¹ * (P i j - ε * J i j) - J i j)
    field_simp
    <;> ring
  calc
    ‖P - J‖ = (1 - ε) * ‖R - J‖ := by
      rw [hdecomp, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    _ ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left (RubikAsymptotics.Spectral.stochastic_residual_norm_le_one R hR) hd.le
    _ < 1 := by linarith

private theorem RubikAsymptotics.Spectral.selfadjoint_gap_of_power_gap {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hs : IsSelfAdjoint A) (hA : ‖A‖ ≤ 1)
    (m : ℕ) (hm : 0 < m) (hp : ‖A ^ m‖ < 1) : ‖A‖ < 1 := by
  have hm2 : m ≤ 2 ^ m := (Nat.lt_two_pow_self (n := m)).le
  have hrest : ‖A ^ (2 ^ m - m)‖ ≤ 1 :=
    (norm_pow_le' A (Nat.sub_pos_of_lt Nat.lt_two_pow_self)).trans
      (pow_le_one₀ (norm_nonneg _) hA)
  have hdyad : ‖A ^ (2 ^ m)‖ < 1 := by
    calc
      ‖A ^ (2 ^ m)‖ = ‖A ^ m * A ^ (2 ^ m - m)‖ := by rw [← pow_add, Nat.add_sub_of_le hm2]
      _ ≤ ‖A ^ m‖ * ‖A ^ (2 ^ m - m)‖ := norm_mul_le _ _
      _ ≤ ‖A ^ m‖ * 1 := mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ < 1 := by simpa using hp
  rw [hs.norm_pow_two_pow m] at hdyad
  by_contra h
  have h1 : 1 ≤ ‖A‖ := le_of_not_gt h
  have hpow : 1 ≤ ‖A‖ ^ (2 ^ m) := one_le_pow₀ h1
  exact (not_lt_of_ge hpow) hdyad

private theorem RubikAsymptotics.Spectral.primitive_symmetric_gap {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n)
    (hs : P.transpose = P)
    (hp : ∃ m : ℕ, 0 < m ∧ ∀ i j, 0 < (P ^ m) i j) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖P - J‖ < 1 := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖P - J‖ < 1
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hPJ : P * J = J := by
    ext i j
    change (∑ k, P i k * (Fintype.card n : ℝ)⁻¹) = _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]
  have hJP : J * P = J := by
    ext i j
    change (∑ k, (Fintype.card n : ℝ)⁻¹ * P k j) = _
    rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic hP j, mul_one]
  have hJJ : J * J = J := by
    ext i j
    change (∑ _ : n, (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹) = (Fintype.card n : ℝ)⁻¹
    simp [hc]
  have hpowJ (k : ℕ) : P ^ k * J = J := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, hPJ, ih]
  have hpow (k : ℕ) : (P - J) ^ (k + 1) = P ^ (k + 1) - J := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, sub_mul, mul_sub, mul_sub, hpowJ, hJP, hJJ,
        sub_self, sub_zero, ← pow_succ]
  have hstarP : IsSelfAdjoint P := by
    change star P = P
    ext i j
    simpa only [Matrix.star_apply, star_trivial, Matrix.transpose_apply] using
      congrArg (fun Q : Matrix n n ℝ => Q i j) hs
  have hstarJ : IsSelfAdjoint J := by
    change star J = J
    ext i j
    change star (J j i) = J i j
    simp [J]
  obtain ⟨m, hm, hpos⟩ := hp
  have hpower : ‖(P - J) ^ m‖ < 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    rw [hpow]
    exact RubikAsymptotics.Spectral.positive_stochastic_gap (P ^ (k + 1)) ((doublyStochastic ℝ n).pow_mem hP _) hpos
  exact RubikAsymptotics.Spectral.selfadjoint_gap_of_power_gap (P - J) (hstarP.sub hstarJ)
    (RubikAsymptotics.Spectral.stochastic_residual_norm_le_one P hP) m hm hpower

private theorem RubikAsymptotics.Spectral.primitive_symmetric_mean_zero_contraction {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (hP : P ∈ doublyStochastic ℝ n) (hs : P.transpose = P)
    (hp : ∃ m : ℕ, 0 < m ∧ ∀ i j, 0 < (P ^ m) i j) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ v : EuclideanSpace ℝ n,
      (∑ i, v i) = 0 →
        ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) P) v‖ ≤ ρ * ‖v‖ := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  refine ⟨‖P - J‖, norm_nonneg _, RubikAsymptotics.Spectral.primitive_symmetric_gap P hP hs hp, ?_⟩
  intro v hv
  have hJv : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) J) v = 0 := by
    ext i
    change (∑ j, (Fintype.card n : ℝ)⁻¹ * v j) = 0
    rw [← Finset.mul_sum, hv, mul_zero]
  have hres : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (P - J)) v =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) P) v := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hJv, sub_zero]
  rw [← hres]
  exact (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (P - J)).le_opNorm v

private theorem RubikAsymptotics.MaxAtom.entry_lt_one_of_residual_norm_lt_one {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hcard : 1 < Fintype.card X) (hP : P ∈ doublyStochastic ℝ X)
    (hgap : let J : Matrix X X ℝ := fun _ _ => (Fintype.card X : ℝ)⁻¹;
      ‖P - J‖ < 1) : ∀ x y, P x y < 1 := by
  classical
  let c : ℝ := (Fintype.card X : ℝ)⁻¹
  let J : Matrix X X ℝ := fun _ _ => c
  let u : EuclideanSpace ℝ X := WithLp.toLp 2 (fun _ => c)
  let v (y : X) : EuclideanSpace ℝ X := EuclideanSpace.single y 1 - u
  have hcpos : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcgt : 1 < (Fintype.card X : ℝ) := by exact_mod_cast hcard
  have hc1 : c < 1 := by
    dsimp [c]
    exact (inv_lt_one₀ hcpos).mpr hcgt
  have hnorm (x y : X) : ‖v x‖ = ‖v y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [v, norm_sub_sq_real, EuclideanSpace.inner_single_left, u]
  have hvmean (y : X) : ∑ i, v y i = 0 := by
    simp [v, u, PiLp.single_apply, Finset.sum_sub_distrib, c, hcpos.ne']
  have hJv (y : X) : (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) J) (v y) = 0 := by
    ext i
    change (∑ j, c * v y j) = 0
    rw [← Finset.mul_sum, hvmean, mul_zero]
  intro x y
  by_contra hnot
  have hxy : P x y = 1 := le_antisymm (le_one_of_mem_doublyStochastic hP) (le_of_not_gt hnot)
  have herase : ∑ i ∈ Finset.univ.erase x, P i y = 0 := by
    have hsum := Finset.sum_erase_add Finset.univ (fun i => P i y) (Finset.mem_univ x)
    rw [sum_col_of_mem_doublyStochastic hP y, hxy] at hsum
    linarith
  have hcol (i : X) : P i y = if i = x then 1 else 0 := by
    by_cases hi : i = x
    · subst i
      simp [hxy]
    · have hz : P i y = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => nonneg_of_mem_doublyStochastic hP)).mp
          herase i (by simp [hi])
      simp [hi, hz]
  have hPv : (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) P) (v y) = v x := by
    rw [show v y = EuclideanSpace.single y 1 - u from rfl, map_sub]
    ext i
    simp only [PiLp.sub_apply, v, u]
    change (∑ j, P i j * (EuclideanSpace.single y 1) j) - (∑ j, P i j * c) =
      (EuclideanSpace.single x 1) i - c
    simp [PiLp.single_apply, mul_ite, ← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP, hcol]
  have hres : (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) (P - J)) (v y) = v x := by
    have hmap : Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) (P - J) =
        Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) P - Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) J :=
      (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ)).map_sub P J
    rw [hmap, ContinuousLinearMap.sub_apply, hPv, hJv, sub_zero]
  have hvpos : 0 < ‖v y‖ := by
    apply norm_pos_iff.mpr
    intro heq
    have heval := congrArg (fun w : EuclideanSpace ℝ X => w y) heq
    have hz : 1 - c = 0 := by simpa [v, u] using heval
    linarith
  have hbound := (Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) (P - J)).le_opNorm (v y)
  rw [hres, hnorm x y] at hbound
  have hstrict : ‖P - J‖ * ‖v y‖ < 1 * ‖v y‖ := mul_lt_mul_of_pos_right hgap hvpos
  change ‖v y‖ ≤ ‖P - J‖ * ‖v y‖ at hbound
  linarith

private theorem RubikAsymptotics.MaxAtom.exists_maxatom_of_residual_norm_lt_one {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hcard : 1 < Fintype.card X) (hP : P ∈ doublyStochastic ℝ X)
    (hgap : let J : Matrix X X ℝ := fun _ _ => (Fintype.card X : ℝ)⁻¹;
      ‖P - J‖ < 1) :
    ∃ a : ℝ, 1 / (Fintype.card X : ℝ) ≤ a ∧ a < 1 ∧ ∀ x y, P x y ≤ a := by
  classical
  let a : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun xy : X × X => P xy.1 xy.2)
  have hupper (x y : X) : P x y ≤ a :=
    Finset.le_sup' (fun xy : X × X => P xy.1 xy.2) (Finset.mem_univ (x,y))
  have halt : a < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
    (fun xy _ => RubikAsymptotics.MaxAtom.entry_lt_one_of_residual_norm_lt_one P hcard hP hgap xy.1 xy.2)
  have hcpos : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  let x : X := Classical.choice inferInstance
  have hsum : 1 ≤ (Fintype.card X : ℝ) * a := by
    calc
      1 = ∑ y, P x y := (sum_row_of_mem_doublyStochastic hP x).symm
      _ ≤ ∑ _ : X, a := Finset.sum_le_sum (fun y _ => hupper x y)
      _ = (Fintype.card X : ℝ) * a := by simp
  exact ⟨a, (div_le_iff₀ hcpos).mpr (by simpa [mul_comm] using hsum), halt, hupper⟩

private theorem RubikAsymptotics.MaxAtom.symmetric_irreducible_selfloop_parameters {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ)
    (hcard : 1 < Fintype.card X) (hP : P ∈ doublyStochastic ℝ X)
    (hs : P.transpose = P)
    (hirr : ∀ x y, ∃ k : ℕ, 0 < (P ^ k) x y)
    (hloop : ∃ z, 0 < P z z) :
    let J : Matrix X X ℝ := fun _ _ => (Fintype.card X : ℝ)⁻¹
    ∃ ρ a : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 / (Fintype.card X : ℝ) ≤ a ∧ a < 1 ∧
      ‖P - J‖ ≤ ρ ∧ ∀ x y, P x y ≤ a := by
  let J : Matrix X X ℝ := fun _ _ => (Fintype.card X : ℝ)⁻¹
  change ∃ ρ a : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 / (Fintype.card X : ℝ) ≤ a ∧ a < 1 ∧
    ‖P - J‖ ≤ ρ ∧ ∀ x y, P x y ≤ a
  have hpower := RubikAsymptotics.Primitive.positive_power_of_irreducible_selfloop P
    (fun _ _ => nonneg_of_mem_doublyStochastic hP) hirr hloop
  have hgap : ‖P - J‖ < 1 := RubikAsymptotics.Spectral.primitive_symmetric_gap P hP hs hpower
  obtain ⟨a, ha, halt, hentries⟩ := RubikAsymptotics.MaxAtom.exists_maxatom_of_residual_norm_lt_one P hcard hP hgap
  refine ⟨(‖P - J‖ + 1) / 2, a, ?_, ?_, ha, halt, ?_, hentries⟩
  all_goals nlinarith [norm_nonneg (P - J)]

open RubikChannel.Paired

private theorem RubikChannel.Paired.state_card_gt_one : 1 < Fintype.card State := by
  let σ : Equiv.Perm (Fin 24) := Equiv.swap 0 20
  let other : State :=
    (⟨Seed ∘ σ, ⟨σ,rfl⟩⟩, seedState.2)
  have hne : seedState ≠ other := by
    intro h
    have he := congrArg (fun x : State => x.1.val (0 : Fin 24)) h
    change RubikGeometry.normalTable 0 = RubikGeometry.normalTable 20 at he
    have hcol : RubikGeometry.normalTable 0 ≠ RubikGeometry.normalTable 20 := by decide
    exact hcol he
  exact Fintype.one_lt_card_iff.mpr ⟨seedState, other, hne⟩
open RubikChannel.Paired
open scoped Matrix.Norms.L2Operator

private theorem RubikChannel.Paired.analytic_parameters :
    let J : Matrix State State ℝ := fun _ _ => (Fintype.card State : ℝ)⁻¹
    1 < Fintype.card State ∧ P ∈ doublyStochastic ℝ State ∧ P.IsSymm ∧
    ∃ ρ a : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 / (Fintype.card State : ℝ) ≤ a ∧ a < 1 ∧
      ‖P - J‖ ≤ ρ ∧ ∀ x y, P x y ≤ a := by
  have hc := RubikChannel.Paired.state_card_gt_one
  obtain ⟨hd,hs,_⟩ := RubikChannel.Paired.primitive
  obtain ⟨hi,hl⟩ := RubikChannel.Paired.irreducible_selfloop
  refine ⟨hc,hd,hs,?_⟩
  exact RubikAsymptotics.MaxAtom.symmetric_irreducible_selfloop_parameters P hc hd hs hi ⟨seedState,hl⟩

open RubikChannel.Paired
open scoped Matrix.Norms.L2Operator

private theorem RubikChannel.Paired.AnalyticParameters :
    let J : Matrix State State ℝ := fun _ _ => (Fintype.card State : ℝ)⁻¹
    1 < Fintype.card State ∧ P ∈ doublyStochastic ℝ State ∧ P.IsSymm ∧
    ∃ ρ a : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 / (Fintype.card State : ℝ) ≤ a ∧ a < 1 ∧
      ‖P - J‖ ≤ ρ ∧ ∀ x y, P x y ≤ a :=
  RubikChannel.Paired.analytic_parameters

open scoped Matrix.Norms.L2Operator
open RubikChannel.Paired

theorem proof_RubikChannel_Paired_universalCodebook (η : ℝ) (hη : 0 < η) : ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ ∃ r : ℝ, 0 < r ∧ (L : ℝ) * r < Real.log (Fintype.card RubikChannel.Paired.State) + η ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ B : RubikCodebook.Book RubikChannel.Paired.Letter k L, RubikCodebook.CoversAll RubikChannel.Paired.act B ∧ ∀ i : Fin L, ((B i).card : ℝ) ≤ Real.exp ((k : ℝ) * r) := by
  obtain ⟨hq, hstoch, hsym, ρ, a, hρ0, hρ1, ha, ha1, hnorm, hentry⟩ :=
    RubikChannel.Paired.AnalyticParameters
  apply RubikUniversal.norm_codebook act ρ a hq hρ0 hρ1 ha ha1
  · simpa only [P, μ] using hentry
  · convert hnorm using 1
    congr 1
    ext x y
    simp only [P, μ, one_div, Matrix.sub_apply, Matrix.of_apply]
    rfl
  · exact hη
