import RubikSTM.Definitions.OBTM.Periodic.SampleLaw
import RubikSTM.Definitions.UniversalCodebooks.PathIndicator
import RubikSTM.Definitions.OBTM.Periodic.LayerwiseUnion
import RubikSTM.Definitions.OBTM.Periodic.UniformMomentBounds
import RubikSTM.Definitions.OBTM.Periodic.CoordinateBounds
import RubikSTM.Definitions.Codebook.Conditional.OverlapLaw
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Channel.Paired.P
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
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

open RubikJanson

private theorem RubikCodebook.Conditional.uniform_reindex_expect {A B : Type*} [Fintype A] [Fintype B]
    (hA : Nonempty A) (hB : Nonempty B) (e : A ≃ B) (G : B → ℝ) :
    (uniformLaw hA).expect (fun x => G (e x)) = (uniformLaw hB).expect G := by
  classical
  change (∑ x, 1 / (Fintype.card A : ℝ) * G (e x)) =
    ∑ y, 1 / (Fintype.card B : ℝ) * G y
  rw [Fintype.card_congr e]
  exact e.sum_comp (fun y => 1 / (Fintype.card B : ℝ) * G y)

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
open Filter Topology

open scoped Classical

private theorem RubikOBTM.Periodic.sampleBook_card {T : ℕ} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p)) {k L M : ℕ}
    (W : RubikOBTM.Periodic.Sample hT K C k L M) (i : Fin L) :
    (RubikOBTM.Periodic.sampleBook hT K C W i).card ≤ M := by
  exact Finset.card_image_le.trans_eq (by simp)

private theorem RubikOBTM.Periodic.sample_covers_iff {T : ℕ} {Z : Type*} (hT : 0 < T)
    (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (W : RubikOBTM.Periodic.Sample hT K C k L M) (x y : Fin k → Z)
    (n : RubikOBTM.Periodic.Profile hT K k L) :
    RubikOBTM.Periodic.CoversPair hT K C act (RubikOBTM.Periodic.sampleBook hT K C W) x y n ↔
      ∃ a : Fin L → Fin M, RubikOBTM.Periodic.endpointEvent hT K C act a x y n W := by
  constructor
  · rintro ⟨w, hw, hxy⟩
    have hx : ∀ i : Fin L, ∃ u : Fin M, W i u = w i := by
      intro i
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp (hw i)
      exact ⟨u, he⟩
    choose a ha using hx
    refine ⟨a, ?_⟩
    change RubikOBTM.Periodic.eval hT K C act n (fun i => W i (a i)) x = y
    simpa only [ha] using hxy
  · rintro ⟨a, ha⟩
    refine ⟨fun i => W i (a i), ?_, ha⟩
    intro i
    exact Finset.mem_image.mpr ⟨a i, Finset.mem_univ _, rfl⟩

private theorem RubikOBTM.Periodic.path_bernoulli {T : ℕ} {Z : Type*} (hT : 0 < T)
    (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (x y : Fin k → Z) (n : RubikOBTM.Periodic.Profile hT K k L) :
    RubikJanson.IsBernoulli (RubikOBTM.Periodic.pathIndicator (M := M) hT K C act x y n) := by
  intro a W
  unfold RubikOBTM.Periodic.pathIndicator
  split <;> simp

private theorem RubikOBTM.Periodic.failure_eq_zeroProb {T : ℕ} {Z : Type*} (hT : 0 < T)
    (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (hC : ∀ p, (C p).Nonempty) (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (x y : Fin k → Z) (n : RubikOBTM.Periodic.Profile hT K k L) :
    (RubikOBTM.Periodic.sampleLaw hT K C hC k L M).prob
      (fun W => ¬ RubikOBTM.Periodic.CoversPair hT K C act
        (RubikOBTM.Periodic.sampleBook hT K C W) x y n) =
      RubikJanson.zeroProb (RubikOBTM.Periodic.sampleLaw hT K C hC k L M)
        (RubikOBTM.Periodic.pathIndicator hT K C act x y n) := by
  unfold RubikJanson.zeroProb RubikJanson.FiniteLaw.prob
  congr 1
  funext W
  have heq : (¬ RubikOBTM.Periodic.CoversPair hT K C act
      (RubikOBTM.Periodic.sampleBook hT K C W) x y n) ↔
      ∀ a : Fin L → Fin M, RubikOBTM.Periodic.pathIndicator hT K C act x y n a W = 0 := by
    simp only [RubikOBTM.Periodic.sample_covers_iff, not_exists,
      RubikOBTM.Periodic.pathIndicator, ite_eq_right_iff, one_ne_zero, imp_false]
  by_cases hz : ∀ a : Fin L → Fin M,
      RubikOBTM.Periodic.pathIndicator hT K C act x y n a W = 0
  · simp only [heq, hz, if_true]
  · simp only [heq, hz, if_false]

open scoped Classical
open RubikJanson RubikCodebook.Conditional

private theorem RubikOBTM.Periodic.path_nonedgeIndependent {T : ℕ} {Z : Type*} (hT : 0 < T)
    (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (hC : ∀ p, (C p).Nonempty) (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ}
    (x y : Fin k → Z) (n : RubikOBTM.Periodic.Profile hT K k L) :
    RubikJanson.NonedgeIndependent (RubikOBTM.Periodic.sampleLaw hT K C hC k L M)
      (RubikOBTM.Periodic.pathIndicator hT K C act x y n) (RubikAggregate.overlapGraph L M) := by
  haveI : ∀ p : Fin T, Nonempty (RubikOBTM.Periodic.Native K C p) := fun p => (hC p).to_subtype
  intro a b hab hno
  have hd : ∀ i, b i ≠ a i := by
    intro i hi
    exact hno ⟨hab, i, hi.symm⟩
  let I := Fin L × Fin M
  let E : I → Type _ := fun t => Fin k → RubikOBTM.Periodic.Native K C (RubikOBTM.Periodic.phase T hT t.1)
  let p : I → Prop := fun t => t.2 = a t.1
  let A := ∀ t : {t : I // p t}, E t.val
  let B := ∀ t : {t : I // ¬ p t}, E t.val
  let f : A → ℝ := fun U =>
    if RubikOBTM.Periodic.eval hT K C act n (fun i => U ⟨(i, a i), rfl⟩) x = y then 1 else 0
  let g : B → ℝ := fun V =>
    if RubikOBTM.Periodic.eval hT K C act n (fun i => V ⟨(i, b i), hd i⟩) x = y then 1 else 0
  let e0 : RubikOBTM.Periodic.Sample hT K C k L M ≃ (∀ t : I, E t) :=
    { toFun := fun W t => W t.1 t.2
      invFun := fun W i u => W (i, u)
      left_inv := by intro W; rfl
      right_inv := by intro W; rfl }
  let e : RubikOBTM.Periodic.Sample hT K C k L M ≃ A × B :=
    e0.trans (Equiv.piEquivPiSubtypeProd p E)
  let P := RubikOBTM.Periodic.sampleLaw hT K C hC k L M
  let PA : FiniteLaw A := uniformLaw inferInstance
  let PB : FiniteLaw B := uniformLaw inferInstance
  let PT : FiniteLaw (A × B) := uniformLaw inferInstance
  have hf (W : RubikOBTM.Periodic.Sample hT K C k L M) :
      RubikOBTM.Periodic.pathIndicator hT K C act x y n a W = f (e W).1 := by
    simp only [RubikOBTM.Periodic.pathIndicator, RubikOBTM.Periodic.endpointEvent, f, e,
      Equiv.trans_apply, e0, Equiv.piEquivPiSubtypeProd]
    split_ifs <;> simp_all
  have hg (W : RubikOBTM.Periodic.Sample hT K C k L M) :
      RubikOBTM.Periodic.pathIndicator hT K C act x y n b W = g (e W).2 := by
    simp only [RubikOBTM.Periodic.pathIndicator, RubikOBTM.Periodic.endpointEvent, g, e,
      Equiv.trans_apply, e0, Equiv.piEquivPiSubtypeProd]
    split_ifs <;> simp_all
  have htransport (H : A × B → ℝ) : P.expect (fun W => H (e W)) = PT.expect H :=
    uniform_reindex_expect inferInstance inferInstance e H
  have hprod : PT.expect (fun z => f z.1 * g z.2) = PA.expect f * PB.expect g := by
    unfold FiniteLaw.expect
    simp only [PT, PA, PB, uniformLaw, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
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
  have hmeanA : RubikJanson.mean P (RubikOBTM.Periodic.pathIndicator hT K C act x y n) a = PA.expect f := by
    change P.expect (fun W => RubikOBTM.Periodic.pathIndicator hT K C act x y n a W) = _
    simp_rw [hf]
    exact (htransport _).trans hleft
  have hmeanB : RubikJanson.mean P (RubikOBTM.Periodic.pathIndicator hT K C act x y n) b = PB.expect g := by
    change P.expect (fun W => RubikOBTM.Periodic.pathIndicator hT K C act x y n b W) = _
    simp_rw [hg]
    exact (htransport _).trans hright
  change P.expect (fun W => RubikOBTM.Periodic.pathIndicator hT K C act x y n a W *
    RubikOBTM.Periodic.pathIndicator hT K C act x y n b W) = _
  simp_rw [hf, hg]
  exact (htransport _).trans (hprod.trans (congrArg₂ (fun u v : ℝ => u * v) hmeanA hmeanB).symm)

open scoped Classical

private theorem RubikOBTM.Periodic.ratio_second_moment_failure {Ω : Type*} [Fintype Ω]
    (P : RubikJanson.FiniteLaw Ω) {L M k : ℕ} (X : (Fin L → Fin M) → Ω → ℝ)
    (r m π α β : ℝ) (R : ℕ → ℝ) (hm : 0 < m)
    (hM : Real.exp ((k : ℝ) * r) / 2 ≤ (M : ℝ)) (hπ : m ^ k ≤ π)
    (hα : α = (L : ℝ) * r + Real.log m) (hR : ∀ s, 0 ≤ R s)
    (hRpos : ∀ j ∈ Finset.Ico 1 L, 0 < R (L-j))
    (hslack : ∀ j ∈ Finset.Ico 1 L, β ≤ (j : ℝ) * r - Real.log (R (L-j)))
    (hmarginal : ∀ a, RubikJanson.mean P X a = π)
    (hjoint : ∀ a b, (RubikAggregate.overlapGraph L M).Adj a b →
      P.expect (fun ω => X a ω * X b ω) ≤
        π ^ 2 * R (L - RubikAggregate.overlapCount a b) ^ k)
    (hX : RubikJanson.IsBernoulli X)
    (hpair : RubikJanson.NonedgeIndependent P X (RubikAggregate.overlapGraph L M)) :
    RubikJanson.zeroProb P X ≤ ((2 : ℝ) ^ L + (3 : ℝ) ^ L) *
      Real.exp (-(k : ℝ) * min α β) := by
  let ν := RubikJanson.nu P X
  let Δ := RubikJanson.Delta P X (RubikAggregate.overlapGraph L M)
  have hπ0 : 0 < π := (pow_pos hm k).trans_le hπ
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hν : ν = (M : ℝ) ^ L * π := RubikAggregate.path_nu_eq P X π hmarginal
  obtain ⟨hν0, hfirst⟩ := RubikMoments.first_moment_lower L k r m M π ν α hm hM hπ hν hα
  have hagg := RubikAggregate.path_Delta_le P X (π ^ 2) R k (sq_nonneg π) hR hjoint
  have hagg' : 2 * (Δ / π ^ 2) ≤ (M : ℝ) ^ L * 1 *
      ∑ j ∈ Finset.Ico 1 L, (L.choose j : ℝ) * (M : ℝ) ^ (L-j) * R (L-j) ^ k := by
    have he : 2 * Δ / π ^ 2 ≤ (M : ℝ) ^ L *
        ∑ j ∈ Finset.Ico 1 L, (L.choose j : ℝ) * (M : ℝ) ^ (L-j) * R (L-j) ^ k := by
      apply (div_le_iff₀ (sq_pos_of_pos hπ0)).mpr
      change 2 * Δ ≤ _
      nlinarith only [hagg]
    simpa only [mul_one, mul_div_assoc] using he
  have hfake := RubikMoments.delta_ratio_bound L k r 1 M 1 ((M : ℝ)^L) (Δ / π^2)
    β R (by norm_num) hM (by simp) (by ring)
    hRpos (by simpa only [div_one] using hslack) hagg'
  have hrat : (Δ / π^2) / ((M : ℝ)^L)^2 = Δ / ν^2 := by
    rw [hν]
    field_simp
    <;> ring
  rw [hrat] at hfake
  have hF := RubikJanson.second_moment_zero P X (RubikAggregate.overlapGraph L M) hX hpair hν0
  exact RubikMoments.second_moment_failure_bound L k ν Δ α β
    (RubikJanson.zeroProb P X) hν0 hfirst hfake hF

open scoped Classical

private theorem RubikOBTM.Periodic.endpoint_profile_card {T : ℕ} {Z : Type*} [Fintype Z]
    (hT : 0 < T) (K : Fin T → Type*) [∀ p, Fintype (K p)] (k L : ℕ) :
    Fintype.card ((Fin k → Z) × (Fin k → Z) × RubikOBTM.Periodic.Profile hT K k L) =
      (Fintype.card Z ^ 2 * ∏ i : Fin L,
        Fintype.card (K (RubikOBTM.Periodic.phase T hT i))) ^ k := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    RubikOBTM.Periodic.Profile, Fintype.card_pi]
  rw [Finset.prod_pow, mul_pow, pow_two, mul_pow]
  ring

private theorem RubikOBTM.Periodic.fixed_samples_cover {T : ℕ} {Z : Type*} [Fintype Z]
    (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)] [∀ p, Fintype (K p)]
    (C : ∀ p, Finset (K p)) (hC : ∀ p, (C p).Nonempty)
    (act : ∀ p, K p →* Equiv.Perm Z) {k L M : ℕ} (R : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hbad : ∀ x y : Fin k → Z, ∀ n : RubikOBTM.Periodic.Profile hT K k L,
      (RubikOBTM.Periodic.sampleLaw hT K C hC k L M).prob
        (fun W => ¬ RubikOBTM.Periodic.CoversPair hT K C act
          (RubikOBTM.Periodic.sampleBook hT K C W) x y n) ≤ b)
    (hsmall : (((Fintype.card Z : ℝ) ^ 2 * ∏ i : Fin L,
      (Fintype.card (K (RubikOBTM.Periodic.phase T hT i)) : ℝ)) ^ k) * b ^ R < 1) :
    ∃ A : RubikOBTM.Periodic.Book hT K C k L, RubikOBTM.Periodic.CoversAll hT K C act A ∧
      ∀ i : Fin L, (A i).card ≤ R * M := by
  haveI : ∀ p : Fin T, Nonempty (RubikOBTM.Periodic.Native K C p) := fun p => (hC p).to_subtype
  let E := (Fin k → Z) × (Fin k → Z) × RubikOBTM.Periodic.Profile hT K k L
  let Ω := RubikOBTM.Periodic.Sample hT K C k L M
  let bad : E → Ω → Prop := fun e W =>
    ¬ RubikOBTM.Periodic.CoversPair hT K C act (RubikOBTM.Periodic.sampleBook hT K C W) e.1 e.2.1 e.2.2
  have hE : (Fintype.card E : ℝ) = ((Fintype.card Z : ℝ) ^ 2 * ∏ i : Fin L,
      (Fintype.card (K (RubikOBTM.Periodic.phase T hT i)) : ℝ)) ^ k := by
    exact_mod_cast RubikOBTM.Periodic.endpoint_profile_card (Z := Z) hT K k L
  have hsmall' : (Fintype.card E : ℝ) * b ^ R < 1 := by rwa [hE]
  obtain ⟨trials, htrials⟩ := RubikJanson.uniform_fixed_trials_cover
    (inferInstance : Nonempty Ω) bad R b hb (fun e => hbad e.1 e.2.1 e.2.2) hsmall'
  let books : Fin R → RubikOBTM.Periodic.Book hT K C k L :=
    fun t => RubikOBTM.Periodic.sampleBook hT K C (trials t)
  refine ⟨RubikOBTM.Periodic.layerwiseUnion hT K C books, ?_, ?_⟩
  · intro x y n
    obtain ⟨t, ht⟩ := htrials (x, y, n)
    have ht' : RubikOBTM.Periodic.CoversPair hT K C act (books t) x y n := by
      simpa only [bad, books, not_not] using ht
    obtain ⟨w, hw, hxy⟩ := ht'
    refine ⟨w, ?_, hxy⟩
    intro i
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hw i⟩
  · intro i
    calc
      (RubikOBTM.Periodic.layerwiseUnion hT K C books i).card ≤ ∑ t : Fin R, (books t i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _t : Fin R, M := Finset.sum_le_sum
        (fun t _ => RubikOBTM.Periodic.sampleBook_card hT K C (trials t) i)
      _ = R * M := by simp

private theorem RubikOBTM.PeriodicRates.ratio_log_upper (q m x : ℝ) (hq : 0 < q) (hm : 0 < m) (hx : 0 ≤ x) :
    0 < min (1 / m) ((1 / q ^ 2 + x) / m ^ 2) ∧
    Real.log (min (1 / m) ((1 / q ^ 2 + x) / m ^ 2)) ≤ -Real.log m ∧
    Real.log (min (1 / m) ((1 / q ^ 2 + x) / m ^ 2)) ≤
      q ^ 2 * x - 2 * (Real.log q + Real.log m) := by
  have hnum : 0 < 1 / q ^ 2 + x := by positivity
  have hR : 0 < min (1 / m) ((1 / q ^ 2 + x) / m ^ 2) := by positivity
  refine ⟨hR, ?_, ?_⟩
  · have hc := Real.log_le_log hR (min_le_left (1 / m) ((1 / q ^ 2 + x) / m ^ 2))
    simpa only [one_div, Real.log_inv] using hc
  · have hc := Real.log_le_log hR (min_le_right (1 / m) ((1 / q ^ 2 + x) / m ^ 2))
    have hid : (1 / q ^ 2 + x) / m ^ 2 = (1 + q ^ 2 * x) / (q * m) ^ 2 := by
      field_simp
      <;> ring
    have hpos : 0 < 1 + q ^ 2 * x := by positivity
    have hlogid : Real.log ((1 / q ^ 2 + x) / m ^ 2) =
        Real.log (1 + q ^ 2 * x) - 2 * (Real.log q + Real.log m) := by
      rw [hid, Real.log_div hpos.ne' (pow_ne_zero 2 (mul_ne_zero hq.ne' hm.ne')),
        Real.log_pow, Real.log_mul hq.ne' hm.ne']
      norm_num
    rw [hlogid] at hc
    have hu := Real.log_le_sub_one_of_pos hpos
    linarith

private theorem RubikOBTM.PeriodicRates.fixed_periodic_overlap_slack (q θ ρ ε : ℝ) (T : ℕ) (hq : 1 < q) (hT : 0 < T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ 4 * T ∣ L ∧ 0 < 1 / q - θ ^ (L / T) ∧
      ∃ α β r : ℝ, 0 < α ∧ 0 < β ∧ 0 < r ∧
        (L : ℝ) * r = Real.log q + ε / 2 ∧
        α = (L : ℝ) * r + Real.log (1 / q - θ ^ (L / T)) ∧ ε / 4 ≤ α ∧
        ∀ j : ℕ, 1 ≤ j → j < L →
          β ≤ (j : ℝ) * r - Real.log
            (min (1 / (1 / q - θ ^ (L / T)))
              ((1 / q ^ 2 + ρ ^ (L - j)) / (1 / q - θ ^ (L / T)) ^ 2)) := by
  have hq0 : 0 < q := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  let a : ℝ := ε / 2
  let h : ℝ := Real.log q + a
  have ha : 0 < a := by dsimp [a]; positivity
  have hh : 0 < h := add_pos (Real.log_pos hq) ha
  have ht : Tendsto (fun n : ℕ => q ^ 2 * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul (q ^ 2)
  obtain ⟨S, hSpow, hS1⟩ :=
    ((ht.eventually (gt_mem_nhds (show 0 < h / 8 by positivity))).and
      (eventually_ge_atTop 1)).exists
  let B : ℝ := min (1 / (2 * q))
    (min (a / (16 * q)) (h / (16 * (q ^ 2 + 4 * q))))
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : B * (2 * q) ≤ 1 := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * q)).mp
    exact min_le_left _ _
  have hBa : B * (16 * q) ≤ a := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * q)).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hBh : B * (16 * (q ^ 2 + 4 * q)) ≤ h := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * (q ^ 2 + 4 * q))).mp
    exact (min_le_right _ _).trans (min_le_right _ _)
  let σ : ℝ := max θ ρ
  have hσ0 : 0 < σ := lt_of_lt_of_le hθ0 (le_max_left _ _)
  have hσ1 : σ < 1 := max_lt hθ1 hρ1
  obtain ⟨K, hK, hK4, hKS, hKA, hKB⟩ :=
    RubikRates.exists_four_layer_scale σ hσ0 hσ1 (2 * S)
      (4 * (S : ℝ) * h / a) (B / (T : ℝ)) (div_pos hB hT0)
  let L : ℕ := T * K
  have hL : 0 < L := Nat.mul_pos hT hK
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hKL : K ≤ L := by
    dsimp [L]
    exact Nat.le_mul_of_pos_left K hT
  have hKS' : 2 * S ≤ L := hKS.trans hKL
  have hKA' : 4 * (S : ℝ) * h / a ≤ L :=
    hKA.trans (by exact_mod_cast hKL)
  have hLT : L / T = K := by dsimp [L]; exact Nat.mul_div_right K hT
  have hL4T : 4 * T ∣ L := by
    obtain ⟨v, hv⟩ := hK4
    refine ⟨v, ?_⟩
    dsimp [L]
    rw [hv]
    ring
  have hLσ : (L : ℝ) * σ ^ (K / 2) < B := by
    have hb := (lt_div_iff₀ hT0).mp hKB
    dsimp [L]
    push_cast
    nlinarith
  have hδpow : θ ^ (L / T) ≤ σ ^ (K / 2) := by
    rw [hLT]
    exact (pow_le_pow_left₀ hθ0.le (le_max_left _ _) K).trans
      (pow_le_pow_of_le_one hσ0.le hσ1.le (Nat.div_le_self K 2))
  have hρpow : ρ ^ (L / 2) ≤ σ ^ (K / 2) := by
    exact (pow_le_pow_left₀ hρ0.le (le_max_right _ _) (L / 2)).trans
      (pow_le_pow_of_le_one hσ0.le hσ1.le (Nat.div_le_div_right hKL))
  have hLδ : (L : ℝ) * θ ^ (L / T) < B :=
    (mul_le_mul_of_nonneg_left hδpow hL0.le).trans_lt hLσ
  have hLρ : (L : ℝ) * ρ ^ (L / 2) < B :=
    (mul_le_mul_of_nonneg_left hρpow hL0.le).trans_lt hLσ
  have hδB : θ ^ (L / T) < B := by
    have hd := mul_le_mul_of_nonneg_right hL1 (pow_nonneg hθ0.le (L / T))
    simpa using hd.trans_lt hLδ
  have hsmall : q * θ ^ (L / T) ≤ 1 / 2 := by
    have hd := mul_lt_mul_of_pos_left hδB hq0
    nlinarith only [hd, hB1]
  let m : ℝ := 1 / q - θ ^ (L / T)
  obtain ⟨hm, hmlo, hmhi⟩ := RubikRates.log_lower_envelope q (θ ^ (L / T)) hq0
    (pow_nonneg hθ0.le (L / T)) hsmall
  let E : ℝ := -2 * (Real.log q + Real.log m)
  have hE0 : 0 ≤ E := by dsimp [E, m]; linarith only [hmhi]
  have hE : E ≤ 4 * q * θ ^ (L / T) := by dsimp [E, m]; linarith only [hmlo]
  have hEa : E ≤ a / 4 := by
    have hd := mul_lt_mul_of_pos_left hδB (show 0 < 4 * q by positivity)
    nlinarith only [hE, hd, hBa]
  have hEh : E ≤ h / 8 := by
    have hd := mul_lt_mul_of_pos_left hδB (show 0 < 4 * q by positivity)
    have hp : 0 ≤ q ^ 2 * B := by positivity
    nlinarith only [hE, hd, hBh, hp, hh]
  have htailmul : (L : ℝ) * (q ^ 2 * ρ ^ (L / 2) + E) ≤ h / 2 := by
    have he := mul_le_mul_of_nonneg_left hE hL0.le
    have hd := mul_lt_mul_of_pos_left hLδ (show 0 < 4 * q by positivity)
    have hp := mul_lt_mul_of_pos_left hLρ (sq_pos_of_pos hq0)
    nlinarith only [he, hd, hp, hBh, hh]
  have htail : q ^ 2 * ρ ^ (L / 2) + E ≤ h / (2 * (L : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (L : ℝ))).mpr
    nlinarith only [htailmul]
  have hSH : (S : ℝ) * h / L ≤ a / 4 := by
    have hs := (div_le_iff₀ ha).mp hKA'
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hs]
  let r : ℝ := h / L
  let β : ℝ := min (a / 2) (min (h / 4) (h / (2 * (L : ℝ))))
  have hr : 0 < r := div_pos hh hL0
  have hβ : 0 < β := by dsimp [β]; positivity
  have hrL : (L : ℝ) * r = h := by dsimp [r]; field_simp
  have hβa : β ≤ a / 2 := min_le_left _ _
  have hβh : β ≤ h / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hβL : β ≤ h / (2 * (L : ℝ)) := (min_le_right _ _).trans (min_le_right _ _)
  have halpha : ε / 4 ≤ h + Real.log m := by
    dsimp [E, h, a] at hEa ⊢
    linarith only [hEa, hε]
  refine ⟨L, hL, hL4T, hm, h + Real.log m, β, r,
    lt_of_lt_of_le (by positivity) halpha, hβ, hr, hrL, ?_, halpha, ?_⟩
  · change h + Real.log m = (L : ℝ) * r + Real.log m
    rw [hrL]
  · intro j hj hjL
    let s : ℕ := L - j
    have hs1 : 1 ≤ s := by dsimp [s]; omega
    have hjs : (j : ℝ) + (s : ℝ) = L := by
      exact_mod_cast (show j + s = L by dsimp [s]; omega)
    obtain ⟨hR, hcap, hbound⟩ := RubikOBTM.PeriodicRates.ratio_log_upper q m (ρ ^ s)
      hq0 hm (pow_nonneg hρ0.le s)
    let b : ℝ := Real.log (min (1 / m) ((1 / q ^ 2 + ρ ^ s) / m ^ 2))
    have hbcap : b ≤ Real.log q + E := by
      change b ≤ -Real.log m at hcap
      dsimp [E] at hE0 ⊢
      linarith only [hcap, hE0]
    have hbpow : b ≤ q ^ 2 * ρ ^ s + E := by
      simpa only [E, sub_eq_add_neg, neg_mul] using hbound
    change β ≤ (j : ℝ) * r - b
    have hjr : (j : ℝ) * r = h - (s : ℝ) * r := by
      calc
        (j : ℝ) * r = ((j : ℝ) + (s : ℝ)) * r - (s : ℝ) * r := by ring
        _ = h - (s : ℝ) * r := by rw [hjs, hrL]
    by_cases hsS : s < S
    · have hsSc : (s : ℝ) ≤ S := by exact_mod_cast hsS.le
      have hSr : (S : ℝ) * r ≤ a / 4 := by simpa [r, mul_div_assoc] using hSH
      have hsr := mul_le_mul_of_nonneg_right hsSc hr.le
      have hid : h - Real.log q = a := by dsimp [h]; ring
      linarith only [hβa, hsr, hSr, hid, hbcap, hEa, hjr]
    · have hSs : S ≤ s := by omega
      by_cases hsHalf : s ≤ L / 2
      · have hs2 : 2 * (s : ℝ) ≤ L := by exact_mod_cast (show 2 * s ≤ L by omega)
        have hmul := mul_le_mul_of_nonneg_right hs2 hr.le
        have hjhalf : h / 2 ≤ (j : ℝ) * r := by linarith only [hmul, hrL, hjr]
        have hps : ρ ^ s ≤ ρ ^ S := pow_le_pow_of_le_one hρ0.le hρ1.le hSs
        have hbsmall : b ≤ h / 8 + E := by
          have hp := mul_le_mul_of_nonneg_left hps (sq_nonneg q)
          linarith only [hbpow, hp, hSpow]
        linarith only [hβh, hjhalf, hbsmall, hEh]
      · have hhs : L / 2 ≤ s := by omega
        have hps : ρ ^ s ≤ ρ ^ (L / 2) := pow_le_pow_of_le_one hρ0.le hρ1.le hhs
        have hbsmall : b ≤ q ^ 2 * ρ ^ (L / 2) + E := by
          have hp := mul_le_mul_of_nonneg_left hps (sq_nonneg q)
          linarith only [hbpow, hp]
        have hjc : (1 : ℝ) ≤ j := by exact_mod_cast hj
        have hjrate := mul_le_mul_of_nonneg_right hjc hr.le
        have hrhalf : h / (2 * (L : ℝ)) = r / 2 := by dsimp [r]; ring
        rw [hrhalf] at htail hβL
        linarith only [hβL, hbsmall, hjrate, htail]

open scoped Classical

private theorem RubikOBTM.Periodic.books_of_estimates {T : ℕ} {Z : Type*} [Fintype Z] [Nonempty Z]
    (hT : 0 < T) (K : Fin T → Type*) [∀ p, Group (K p)] [∀ p, Fintype (K p)]
    (C : ∀ p, Finset (K p)) (hC : ∀ p, (C p).Nonempty)
    (act : ∀ p, K p →* Equiv.Perm Z) (L : ℕ) (r m α β ε : ℝ) (R : ℕ → ℝ)
    (hQ : 1 < Fintype.card Z) (hL : 0 < L) (hr : 0 < r) (hm : 0 < m)
    (hα : α = (L : ℝ) * r + Real.log m) (hαpos : 0 < α) (hβpos : 0 < β)
    (hε : 0 < ε) (hrate : (L : ℝ) * r = Real.log (Fintype.card Z) + ε / 2)
    (hR : ∀ s, 0 ≤ R s) (hRpos : ∀ j ∈ Finset.Ico 1 L, 0 < R (L-j))
    (hslack : ∀ j ∈ Finset.Ico 1 L, β ≤ (j : ℝ) * r - Real.log (R (L-j)))
    (hest : RubikOBTM.Periodic.MomentEstimates hT K C hC act L m R) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ A : RubikOBTM.Periodic.Book hT K C k L,
      RubikOBTM.Periodic.CoversAll hT K C act A ∧ (∀ i, (A i).Nonempty) ∧
        ∀ i : Fin L, ((A i).card : ℝ) ≤
          Real.exp ((k : ℝ) * (Real.log (Fintype.card Z) + ε) / (L : ℝ)) := by
  let q : ℝ := Fintype.card Z
  let F : ℝ := (2 : ℝ) ^ L + (3 : ℝ) ^ L
  let γ : ℝ := min α β
  let B : ℝ := q ^ 2 * ∏ i : Fin L, (Fintype.card (K (RubikOBTM.Periodic.phase T hT i)) : ℝ)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast hQ
  have hprod : (1 : ℝ) ≤ ∏ i : Fin L,
      (Fintype.card (K (RubikOBTM.Periodic.phase T hT i)) : ℝ) := by
    apply Finset.one_le_prod
    intro i _
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K (RubikOBTM.Periodic.phase T hT i)))
  have hB : 1 < B := by
    dsimp [B]
    have hp := mul_le_mul_of_nonneg_left hprod (sq_nonneg q)
    nlinarith only [hp, hq]
  have hF : 0 < F := by dsimp [F]; positivity
  have hγ : 0 < γ := lt_min hαpos hβpos
  obtain ⟨N, hN, hgap, k1, hk1⟩ := RubikMoments.fixed_amplification_union_tail B F γ hB hF hγ
  obtain ⟨k2, hk2⟩ := RubikMoments.floor_exp_half_tail r hr
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨k3, hk3⟩ := RubikRates.fixed_codebook_factor_absorbed q ε (N : ℝ) L hε hNreal hL
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨max k1 (max k2 k3), fun k hk => ?_⟩
  have hh1 : k1 ≤ k := le_trans (le_max_left _ _) hk
  have hh2 : k2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hh3 : k3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  let M := ⌊Real.exp ((k : ℝ) * r)⌋₊
  have hM : Real.exp ((k : ℝ) * r) / 2 ≤ (M : ℝ) := hk2 k hh2
  have hbad : ∀ x y : Fin k → Z, ∀ n : RubikOBTM.Periodic.Profile hT K k L,
      (RubikOBTM.Periodic.sampleLaw hT K C hC k L M).prob
        (fun W => ¬ RubikOBTM.Periodic.CoversPair hT K C act
          (RubikOBTM.Periodic.sampleBook hT K C W) x y n) ≤ F * Real.exp (-(k : ℝ) * γ) := by
    intro x y n
    obtain ⟨π, hπ, hmean, hjoint⟩ := hest k M x y n
    rw [RubikOBTM.Periodic.failure_eq_zeroProb]
    exact RubikOBTM.Periodic.ratio_second_moment_failure _ _ r m π α β R hm hM hπ hα
      hR hRpos hslack hmean hjoint (RubikOBTM.Periodic.path_bernoulli hT K C act x y n)
      (RubikOBTM.Periodic.path_nonedgeIndependent hT K C hC act x y n)
  have hsmall : B ^ k * (F * Real.exp (-(k : ℝ) * γ)) ^ N < 1 := by
    have hp : B ^ k ≤ B ^ (2 * k) := pow_le_pow_right₀ hB.le (by omega)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hp (by positivity)) (hk1 k hh1)
  obtain ⟨A, hcover, hsize⟩ := RubikOBTM.Periodic.fixed_samples_cover hT K C hC act N
    (F * Real.exp (-(k : ℝ) * γ)) (by positivity) hbad hsmall
  have hnonempty : ∀ i, (A i).Nonempty := by
    let z : Z := Classical.choice inferInstance
    let n : RubikOBTM.Periodic.Profile hT K k L := fun _ _ => 1
    obtain ⟨w, hw, _⟩ := hcover (fun _ => z) (fun _ => z) n
    exact fun i => ⟨w i, hw i⟩
  refine ⟨A, hcover, hnonempty, fun i => ?_⟩
  have hnat : ((A i).card : ℝ) ≤ (N : ℝ) * (M : ℝ) := by exact_mod_cast hsize i
  have hfloor : (M : ℝ) ≤ Real.exp ((k : ℝ) * r) := Nat.floor_le (Real.exp_pos _).le
  have hkr : (k : ℝ) * r = (k : ℝ) * (Real.log q + ε / 2) / (L : ℝ) := by
    change (k : ℝ) * r = (k : ℝ) * (Real.log (Fintype.card Z) + ε / 2) / (L : ℝ)
    rw [← hrate]
    field_simp
  calc
    ((A i).card : ℝ) ≤ (N : ℝ) * (M : ℝ) := hnat
    _ ≤ (N : ℝ) * Real.exp ((k : ℝ) * r) := mul_le_mul_of_nonneg_left hfloor hNreal.le
    _ = (N : ℝ) * Real.exp ((k : ℝ) * (Real.log q + ε / 2) / (L : ℝ)) := by rw [hkr]
    _ ≤ Real.exp ((k : ℝ) * (Real.log q + ε) / (L : ℝ)) := hk3 k hh3
open scoped Classical

private theorem RubikOBTM.Periodic.entropy_books_of_uniform_moments {T : ℕ} {Z : Type*}
    [Fintype Z] [Nonempty Z] (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] [∀ p, Fintype (K p)] (C : ∀ p, Finset (K p))
    (hC : ∀ p, (C p).Nonempty) (act : ∀ p, K p →* Equiv.Perm Z)
    (θ ρ : ℝ) (hQ : 1 < Fintype.card Z) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbound : RubikOBTM.Periodic.UniformMomentBounds hT K C hC act θ ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ 4 * T ∣ L ∧ ∃ r : ℝ, 0 < r ∧
      (L : ℝ) * r < Real.log (Fintype.card Z) + ε ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ A : RubikOBTM.Periodic.Book hT K C k L,
        RubikOBTM.Periodic.CoversAll hT K C act A ∧ (∀ i, (A i).Nonempty) ∧
          ∀ i : Fin L, ((A i).card : ℝ) ≤ Real.exp ((k : ℝ) * r) := by
  let q : ℝ := Fintype.card Z
  have hq : 1 < q := by dsimp [q]; exact_mod_cast hQ
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨L, hL, hLT, hm, α, β, r0, hαpos, hβpos, hr0, hrate, hα, hlo, hslack⟩ :=
    RubikOBTM.PeriodicRates.fixed_periodic_overlap_slack q θ ρ (ε / 2) T hq hT
      hθ0 hθ1 hρ0 hρ1 hε2
  let m : ℝ := RubikOBTM.Periodic.lowerEnvelope q θ L T
  let R := RubikOBTM.Periodic.ratioEnvelope q m ρ
  have hTd : T ∣ L := dvd_trans (dvd_mul_left T 4) hLT
  have hest : RubikOBTM.Periodic.MomentEstimates hT K C hC act L m R := hbound L hL hTd hm
  have hRpos (s : ℕ) : 0 < R s := by
    exact (RubikOBTM.PeriodicRates.ratio_log_upper q m (ρ ^ s)
      (lt_trans zero_lt_one hq) hm (pow_nonneg hρ0.le s)).1
  obtain ⟨k0, hk0⟩ := RubikOBTM.Periodic.books_of_estimates hT K C hC act L r0 m α β (ε / 2) R
    hQ hL hr0 hm hα hαpos hβpos hε2 hrate (fun s => (hRpos s).le)
    (fun j _ => hRpos (L-j))
    (fun j hj => hslack j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2) hest
  let r : ℝ := (Real.log q + ε / 2) / (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : 0 < r := div_pos (add_pos (Real.log_pos hq) hε2) hLreal
  have hLr : (L : ℝ) * r = Real.log q + ε / 2 := by dsimp [r]; field_simp
  refine ⟨L, hL, hLT, r, hr, ?_, k0, fun k hk => ?_⟩
  · change (L : ℝ) * r < Real.log q + ε
    rw [hLr]
    linarith only [hε]
  · obtain ⟨A, hcover, hnonempty, hsize⟩ := hk0 k hk
    refine ⟨A, hcover, hnonempty, fun i => ?_⟩
    simpa only [r, mul_div_assoc] using hsize i

open RubikJanson RubikCodebook.Conditional RubikOBTM.Periodic
open scoped Classical

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

private theorem RubikOBTM.PeriodicCoupling.two_paths_expect {E : Type*} [Fintype E] [Nonempty E]
    {L M : ℕ} (a b : Fin L → Fin M) (f g : (Fin L → E) → ℝ) :
    (RubikJanson.uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).expect
      (fun W => f (fun i => W (i, a i)) * g (fun i => W (i, b i))) =
    (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → E × E))).expect
      (fun v => f (fun i => (v i).1) *
        g (fun i => if a i = b i then (v i).1 else (v i).2)) := by
  classical
  have pullback {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (t : B → A) (ht : Function.Injective t) (H : (B → E) → ℝ) :
      (uniformLaw (inferInstance : Nonempty (A → E))).expect
          (fun W => H (fun j => W (t j))) =
        (uniformLaw (inferInstance : Nonempty (B → E))).expect H := by
    classical
    letI : DecidablePred (Set.range t) := fun _ => Classical.propDecidable _
    let e : B ≃ Set.range t := Equiv.ofInjective t ht
    let C := {i : A // i ∉ Set.range t} → E
    let c : (A → E) ≃ (B → E) × C :=
      (Equiv.piEquivPiSubtypeProd (Set.range t) (fun _ => E)).trans
        (Equiv.prodCongr (Equiv.arrowCongr e.symm (Equiv.refl E)) (Equiv.refl C))
    have hc (W : A → E) : (c W).1 = fun j => W (t j) := by
      funext j
      rfl
    simpa only [hc] using
      (uniform_reindex_expect inferInstance inferInstance c (fun z => H z.1)).trans
        (uniform_prod_fst_expect inferInstance inferInstance inferInstance H)
  let S := {i : Fin L // a i ≠ b i}
  let D := Fin L ⊕ S
  let d : D → Fin L × Fin M := Sum.elim (fun i => (i, a i)) (fun i => (i.val, b i.val))
  have hd : Function.Injective d := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (congrArg Prod.fst hxy)
    · have hij : i = j.val := congrArg Prod.fst hxy
      have hab : a i = b j.val := congrArg Prod.snd hxy
      exact (j.property (by simpa only [hij] using hab)).elim
    · have hij : i.val = j := congrArg Prod.fst hxy
      have hba : b i.val = a j := congrArg Prod.snd hxy
      exact (i.property (by simpa only [← hij] using hba.symm)).elim
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg Prod.fst hxy
  let p : D → Fin L × Bool := Sum.elim (fun i => (i, false)) (fun i => (i.val, true))
  have hp : Function.Injective p := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (congrArg Prod.fst hxy)
    · have hf : (false : Bool) = true := congrArg Prod.snd hxy
      cases hf
    · have hf : (true : Bool) = false := congrArg Prod.snd hxy
      cases hf
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg Prod.fst hxy
  let H : (D → E) → ℝ := fun z =>
    f (fun i => z (Sum.inl i)) *
      g (fun i => if hi : a i = b i then z (Sum.inl i) else z (Sum.inr ⟨i, hi⟩))
  have hdict (W : (Fin L × Fin M) → E) :
      H (fun u => W (d u)) = f (fun i => W (i, a i)) * g (fun i => W (i, b i)) := by
    dsimp only [H, d, Sum.elim_inl, Sum.elim_inr]
    congr 1
    apply congrArg g
    funext i
    by_cases hi : a i = b i
    · simp [hi]
    · simp only [dif_neg hi]
  let e : ((Fin L × Bool) → E) ≃ (Fin L → E × E) :=
    { toFun := fun W i => (W (i, false), W (i, true))
      invFun := fun v z => if z.2 then (v z.1).2 else (v z.1).1
      left_inv := by
        intro W
        funext z
        rcases z with ⟨i, c⟩
        cases c <;> rfl
      right_inv := by
        intro v
        funext i
        exact Prod.eta (v i) }
  let J : (Fin L → E × E) → ℝ := fun v =>
    f (fun i => (v i).1) * g (fun i => if a i = b i then (v i).1 else (v i).2)
  have hpairs (W : (Fin L × Bool) → E) : H (fun u => W (p u)) = J (e W) := by
    dsimp only [H, p, J, e, Sum.elim_inl, Sum.elim_inr, Equiv.coe_fn_mk]
    congr 1
  calc
    _ = (uniformLaw (inferInstance : Nonempty (D → E))).expect H := by
      simpa only [hdict] using pullback d hd H
    _ = (uniformLaw (inferInstance : Nonempty ((Fin L × Bool) → E))).expect
          (fun W => J (e W)) := by
      simpa only [hpairs] using (pullback p hp H).symm
    _ = _ := uniform_reindex_expect inferInstance inferInstance e J

open RubikJanson
open scoped Classical

private theorem RubikOBTM.PeriodicCoupling.uniform_pi_prob_all {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (k : ℕ) (event : Fin k → Ω → Prop) :
    (uniformLaw (inferInstance : Nonempty (Fin k → Ω))).prob
      (fun w => ∀ j, event j (w j)) =
    ∏ j : Fin k, (uniformLaw (inferInstance : Nonempty Ω)).prob (event j) := by
  classical
  have hweight : (1 : ℝ) / Fintype.card (Fin k → Ω) =
      ∏ _ : Fin k, (1 : ℝ) / Fintype.card Ω := by
    simp [Fintype.card_fun, div_pow]
  unfold FiniteLaw.prob FiniteLaw.expect
  simp only [uniformLaw]
  rw [hweight, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : ∀ j, event j (w j)
  · simp [h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hz : (∏ j, ((1 : ℝ) / Fintype.card Ω) *
        (if event j (w j) then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    simpa only [h, if_false, mul_zero] using hz.symm

universe u v

private theorem RubikOBTM.Periodic.uniform_moments_of_coordinate {T : ℕ} {K0 : Type u} {Z : Type v}
    [Group K0] [Fintype Z] [Nonempty Z]
    (hT : 0 < T) (C0 : Finset K0) (hC0 : C0.Nonempty)
    (act : Fin T → K0 →* Equiv.Perm Z) (θ ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcoords : RubikOBTM.Periodic.CoordinateBounds hT C0 hC0 act θ ρ) :
    RubikOBTM.Periodic.UniformMomentBounds hT (fun _ => K0) (fun _ => C0)
      (fun _ => hC0) act θ ρ := by
  classical
  let E := NativeConstant C0
  letI : Nonempty E := hC0.to_subtype
  have hmul (P Q : Prop) : ((if P then 1 else 0) : ℝ) * (if Q then 1 else 0) =
      if P ∧ Q then 1 else 0 := by
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  have probnonneg {A : Type u} [Fintype A] (P : FiniteLaw A) (V : A → Prop) :
      0 ≤ P.prob V := by
    unfold FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_nonneg
    intro w _
    exact mul_nonneg (P.nonneg w) (show (0 : ℝ) ≤ if V w then 1 else 0 by split_ifs <;> norm_num)
  have probmono {A : Type u} [Fintype A] (P : FiniteLaw A) (V U : A → Prop)
      (h : ∀ w, V w → U w) : P.prob V ≤ P.prob U := by
    unfold FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left _ (P.nonneg w)
    by_cases hv : V w
    · simp [hv, h w hv]
    · by_cases hu : U w <;> simp [hv, hu]
  have reindexProb {A B : Type u} [Fintype A] [Fintype B]
      [Nonempty A] [Nonempty B] (e : A ≃ B) (V : B → Prop) :
      (uniformLaw (inferInstance : Nonempty A)).prob (fun a => V (e a)) =
      (uniformLaw (inferInstance : Nonempty B)).prob V := by
    unfold FiniteLaw.prob
    exact uniform_reindex_expect inferInstance inferInstance e (fun w => if V w then (1 : ℝ) else 0)
  have probAnd {A : Type u} [Fintype A] (P : FiniteLaw A) (V U : A → Prop) :
      P.prob (fun w => V w ∧ U w) =
      P.expect (fun w => (if V w then (1 : ℝ) else 0) * (if U w then 1 else 0)) := by
    unfold FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro w _
    by_cases hv : V w <;> by_cases hu : U w <;> simp [hv, hu]
  have firstdraw {L : ℕ} (H : (Fin L → E) → ℝ) :
      (uniformLaw (inferInstance : Nonempty (Fin L → E × E))).expect
        (fun v => H (fun i => (v i).1)) =
      (uniformLaw (inferInstance : Nonempty (Fin L → E))).expect H := by
    let e : (Fin L → E × E) ≃ (Fin L → E) × (Fin L → E) :=
      { toFun := fun v => (fun i => (v i).1, fun i => (v i).2)
        invFun := fun p i => (p.1 i, p.2 i)
        left_inv := by intro v; funext i; exact Prod.eta (v i)
        right_inv := by intro p; rfl }
    exact (uniform_reindex_expect inferInstance inferInstance e (fun p => H p.1)).trans
      (uniform_prod_fst_expect inferInstance inferInstance inferInstance H)
  have firstdrawProb {L : ℕ} (V : (Fin L → E) → Prop) :
      (uniformLaw (inferInstance : Nonempty (Fin L → E × E))).prob
        (fun v => V (fun i => (v i).1)) =
      (uniformLaw (inferInstance : Nonempty (Fin L → E))).prob V := by
    unfold FiniteLaw.prob
    exact firstdraw (fun w => if V w then (1 : ℝ) else 0)
  have dictionarySingle {L M : ℕ} (a : Fin L → Fin M) (V : (Fin L → E) → Prop) :
      (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob
        (fun W => V (fun i => W (i, a i))) =
      (uniformLaw (inferInstance : Nonempty (Fin L → E))).prob V := by
    have hc := RubikOBTM.PeriodicCoupling.two_paths_expect a a
      (fun w => if V w then (1 : ℝ) else 0) (fun _ => (1 : ℝ))
    simp only [mul_one] at hc
    exact hc.trans (firstdraw (fun w => if V w then (1 : ℝ) else 0))
  have dictionaryJointEvent {L M : ℕ} (a b : Fin L → Fin M)
      (V U : (Fin L → E) → Prop) :
      (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob
        (fun W => V (fun i => W (i, a i)) ∧ U (fun i => W (i, b i))) =
      (uniformLaw (inferInstance : Nonempty (Fin L → E × E))).prob
        (fun v => V (fun i => (v i).1) ∧ U (fun i => if a i = b i then (v i).1 else (v i).2)) := by
    exact (probAnd _ _ _).trans
      ((RubikOBTM.PeriodicCoupling.two_paths_expect a b
        (fun w => if V w then (1 : ℝ) else 0)
        (fun w => if U w then (1 : ℝ) else 0)).trans (probAnd _ _ _).symm)
  have dictionaryJoint {L M : ℕ} (a b : Fin L → Fin M)
      (n : Fin L → K0) (x y : Z) :
      (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob
        (fun W => coordinateRun hT C0 act n (fun i => W (i, a i)) x = y ∧
          coordinateRun hT C0 act n (fun i => W (i, b i)) x = y) =
      coordinateJointProb hT C0 hC0 act n (fun i => decide (a i = b i)) x y := by
    have hc := dictionaryJointEvent a b (fun w => coordinateRun hT C0 act n w x = y)
      (fun w => coordinateRun hT C0 act n w x = y)
    simpa only [coordinateJointProb, decide_eq_true_eq] using hc
  have jointSingle {L : ℕ} (n : Fin L → K0) (shared : Fin L → Bool) (x y : Z) :
      coordinateJointProb hT C0 hC0 act n shared x y ≤ coordinateProb hT C0 hC0 act n x y := by
    unfold coordinateJointProb coordinateProb
    calc
      _ ≤ (uniformLaw (inferInstance : Nonempty (Fin L → E × E))).prob
          (fun v => coordinateRun hT C0 act n (fun i => (v i).1) x = y) :=
        probmono _ _ _ (fun _ h => h.1)
      _ = _ := firstdrawProb (fun w => coordinateRun hT C0 act n w x = y)
  have rows {k L M : ℕ} (V : Fin k → ((Fin L × Fin M) → E) → Prop) :
      (sampleLaw hT (fun _ => K0) (fun _ => C0) (fun _ => hC0) k L M).prob
        (fun W => ∀ z, V z (fun ij => W ij.1 ij.2 z)) =
      ∏ z : Fin k, (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob (V z) := by
    let e : Sample hT (fun _ => K0) (fun _ => C0) k L M ≃
        (Fin k → (Fin L × Fin M) → E) :=
      { toFun := fun W z ij => W ij.1 ij.2 z
        invFun := fun V i u z => V z (i, u)
        left_inv := by intro W; rfl
        right_inv := by intro V; rfl }
    exact (reindexProb e (fun V' => ∀ z, V z (V' z))).trans
      (RubikOBTM.PeriodicCoupling.uniform_pi_prob_all k V)
  have scalar (p d m A : ℝ) (hm : 0 < m) (hmp : m ≤ p)
      (hd0 : 0 ≤ d) (hdp : d ≤ p) (hdA : d ≤ A) :
      d ≤ p ^ 2 * min (1 / m) (A / m ^ 2) := by
    have hp : 0 < p := hm.trans_le hmp
    have hA : 0 ≤ A := hd0.trans hdA
    have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
    have hpp : m ^ 2 ≤ p ^ 2 := by nlinarith
    have h1 : d ≤ p ^ 2 * (1 / m) := by
      apply hdp.trans
      rw [mul_one_div]
      apply (le_div_iff₀ hm).mpr
      nlinarith
    have h2 : d ≤ p ^ 2 * (A / m ^ 2) := by
      have hc := mul_le_mul_of_nonneg_right hpp (div_nonneg hA hm2.le)
      have hid : m ^ 2 * (A / m ^ 2) = A := by field_simp
      rw [hid] at hc
      exact hdA.trans hc
    rcases le_total (1 / m) (A / m ^ 2) with hh | hh
    · rw [min_eq_left hh]; exact h1
    · rw [min_eq_right hh]; exact h2
  unfold UniformMomentBounds MomentEstimates
  intro L hL hTL hm k M x y n
  let p : Fin k → ℝ := fun z => coordinateProb hT C0 hC0 act (fun i => n i z) (x z) (y z)
  let m := lowerEnvelope (Fintype.card Z) θ L T
  let P : Fin k → (Fin L → E) → Prop := fun z w =>
    coordinateRun hT C0 act (fun i => n i z) w (x z) = y z
  have hp (z : Fin k) : m ≤ p z := (hcoords L hL hTL (fun i => n i z) (x z) (y z)).1
  have hp0 (z : Fin k) : 0 ≤ p z := hm.le.trans (hp z)
  have hevent (a : Fin L → Fin M) (W : Sample hT (fun _ => K0) (fun _ => C0) k L M) :
      endpointEvent hT (fun _ => K0) (fun _ => C0) act a x y n W ↔
        ∀ z, P z (fun i => W i (a i) z) := by
    change ((fun z => coordinateRun hT C0 act (fun i => n i z)
      (fun i => W i (a i) z) (x z)) = y) ↔ _
    exact funext_iff
  refine ⟨∏ z, p z, ?_, ?_, ?_⟩
  · have hc := Finset.prod_le_prod (fun z (_ : z ∈ (Finset.univ : Finset (Fin k))) => hm.le)
      (fun z (_ : z ∈ (Finset.univ : Finset (Fin k))) => hp z)
    simpa using hc
  · intro a
    change (sampleLaw hT (fun _ => K0) (fun _ => C0) (fun _ => hC0) k L M).prob
      (fun W => endpointEvent hT (fun _ => K0) (fun _ => C0) act a x y n W) = _
    have heq : (fun W => endpointEvent hT (fun _ => K0) (fun _ => C0) act a x y n W) =
        (fun W => ∀ z, P z (fun i => W i (a i) z)) := by
      funext W
      exact propext (hevent a W)
    rw [heq]
    calc
      _ = ∏ z : Fin k, (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob
          (fun W => P z (fun i => W (i, a i))) := rows (fun z W => P z (fun i => W (i, a i)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro z _
        exact dictionarySingle a (P z)
  · intro a b _hab
    let shared : Fin L → Bool := fun i => decide (a i = b i)
    have hshared : (Finset.univ.filter (fun i => shared i = false)).card =
        L - RubikAggregate.overlapCount a b := by
      have heq : Finset.univ.filter (fun i => shared i = false) =
          Finset.univ \ Finset.univ.filter (fun i => b i = a i) := by
        ext i
        simp [shared, eq_comm]
      rw [heq, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ, Fintype.card_fin]
      rfl
    let s := L - RubikAggregate.overlapCount a b
    let A : ℝ := 1 / (Fintype.card Z : ℝ) ^ 2 + ρ ^ s
    let R : ℝ := ratioEnvelope (Fintype.card Z) m ρ s
    let d : Fin k → ℝ := fun z => coordinateJointProb hT C0 hC0 act
      (fun i => n i z) shared (x z) (y z)
    have hd0 (z : Fin k) : 0 ≤ d z := probnonneg _ _
    have hdp (z : Fin k) : d z ≤ p z := jointSingle _ _ _ _
    have hdA (z : Fin k) : d z ≤ A := by
      have hc := (hcoords L hL hTL (fun i => n i z) (x z) (y z)).2 shared
      simpa only [hshared] using hc
    have hd (z : Fin k) : d z ≤ p z ^ 2 * R :=
      scalar (p z) (d z) m A hm (hp z) (hd0 z) (hdp z) (hdA z)
    have hexpect :
        (sampleLaw hT (fun _ => K0) (fun _ => C0) (fun _ => hC0) k L M).expect
          (fun W => pathIndicator hT (fun _ => K0) (fun _ => C0) act x y n a W *
            pathIndicator hT (fun _ => K0) (fun _ => C0) act x y n b W) = ∏ z, d z := by
      calc
        _ = (sampleLaw hT (fun _ => K0) (fun _ => C0) (fun _ => hC0) k L M).prob
            (fun W => ∀ z, P z (fun i => W i (a i) z) ∧ P z (fun i => W i (b i) z)) := by
          unfold FiniteLaw.prob FiniteLaw.expect
          apply Finset.sum_congr rfl
          intro W _
          have ha := hevent a W
          have hb := hevent b W
          by_cases hA : ∀ z, P z (fun i => W i (a i) z) <;>
            by_cases hB : ∀ z, P z (fun i => W i (b i) z) <;>
            simp [pathIndicator, ha, hb, forall_and, hA, hB]
        _ = ∏ z, d z := by
          calc
            _ = ∏ z : Fin k, (uniformLaw (inferInstance : Nonempty ((Fin L × Fin M) → E))).prob
                (fun W => P z (fun i => W (i, a i)) ∧ P z (fun i => W (i, b i))) :=
              rows (fun z W => P z (fun i => W (i, a i)) ∧ P z (fun i => W (i, b i)))
            _ = _ := by
              apply Finset.prod_congr rfl
              intro z _
              exact dictionaryJoint a b (fun i => n i z) (x z) (y z)
    rw [hexpect]
    calc
      (∏ z, d z) ≤ ∏ z, p z ^ 2 * R := Finset.prod_le_prod (fun z _ => hd0 z) (fun z _ => hd z)
      _ = (∏ z, p z) ^ 2 * ratioEnvelope (Fintype.card Z)
          (lowerEnvelope (Fintype.card Z) θ L T) ρ (L - RubikAggregate.overlapCount a b) ^ k := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
        simp [R, m, s]

open Rubik RubikGeometry
private theorem RubikGeometry.card_normalTable_orbit :
    Nat.card {f : Fin 24 → Normal // ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      orbitColourings := by
  classical
  let G := DomMulAct (Equiv.Perm (Fin 24))
  have heq : {f : Fin 24 → Normal | ∃ σ : Equiv.Perm (Fin 24), f = normalTable ∘ σ} =
      MulAction.orbit G normalTable := by
    ext f
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨DomMulAct.mk σ, rfl⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨DomMulAct.mk.symm σ, hσ.symm⟩
  have hfib : ∀ c : Normal, Fintype.card {i : Fin 24 // normalTable i = c} = 4 := by
    decide
  have hstab : Nat.card (MulAction.stabilizer G normalTable) = (Nat.factorial 4) ^ 6 := by
    calc
      _ = Nat.card {g : Equiv.Perm (Fin 24) // normalTable ∘ g = normalTable} :=
        Nat.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => Iff.rfl))
      _ = ∏ c : Normal, (Fintype.card {i : Fin 24 // normalTable i = c}).factorial := by
        rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
      _ = (Nat.factorial 4) ^ 6 := by simp [hfib, Rubik.Normal]
  have hG : Nat.card G = Nat.factorial 24 := by
    rw [Nat.card_congr DomMulAct.mk.symm, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G normalTable)
  rw [Nat.card_prod, hstab, hG] at hos
  calc
    _ = Nat.card (MulAction.orbit G normalTable) := Nat.card_congr (Equiv.setCongr heq)
    _ = orbitColourings := by
      unfold orbitColourings
      exact Nat.eq_div_of_mul_eq_right (by positivity) (by simpa [Nat.mul_comm] using hos)

private theorem RubikChannel.Paired.StateCard :
    Fintype.card RubikChannel.Paired.State = RubikGeometry.orbitColourings ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (RubikChannel.Colour.Orbit RubikGeometry.normalTable ×
    RubikChannel.Colour.Orbit RubikGeometry.normalTable) = RubikGeometry.orbitColourings ^ 2
  rw [Nat.card_prod]
  change Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24),
    f = RubikGeometry.normalTable ∘ σ} *
    Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24),
    f = RubikGeometry.normalTable ∘ σ} = RubikGeometry.orbitColourings ^ 2
  rw [RubikGeometry.card_normalTable_orbit, pow_two]

private theorem RubikChannel.Paired.log_card_div_eight :
    Real.log (Fintype.card RubikChannel.Paired.State : ℝ) / 8 = Rubik.entropyConstant := by
  have hq : (RubikGeometry.orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ) ^ 6 := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  rw [RubikChannel.Paired.StateCard, Nat.cast_pow, Real.log_pow, hq]
  unfold Rubik.entropyConstant
  ring

open scoped Classical

theorem proof_RubikOBTM_Periodic_native_book_supply_of_coordinates
    (hT : 0 < RubikOBTM.Finite.period) (hC : RubikOBTM.Finite.nativeC.Nonempty)
    (θ ρ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hcoords : RubikOBTM.Periodic.CoordinateBounds hT RubikOBTM.Finite.nativeC hC
      RubikOBTM.Finite.periodicAct θ ρ) : RubikOBTM.Global.BookSupply := by
  have hQ : 1 < Fintype.card RubikOBTM.Finite.Z := by
    change 1 < Fintype.card RubikChannel.Paired.State
    rw [RubikChannel.Paired.StateCard]
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hcard : (Fintype.card RubikOBTM.Finite.Z : ℝ) = RubikCostBridge.q ^ 2 := by
    have hc : Nat.card RubikChannel.Paired.State =
        Nat.card (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed) *
        Nat.card (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed) := Nat.card_prod _ _
    simp only [Nat.card_eq_fintype_card] at hc
    dsimp [RubikCostBridge.q]
    rw [pow_two]
    exact_mod_cast hc
  have hmoment := RubikOBTM.Periodic.uniform_moments_of_coordinate hT RubikOBTM.Finite.nativeC hC
    RubikOBTM.Finite.periodicAct θ ρ hρ0.le hcoords
  intro η hη
  obtain ⟨L, hL, hLT, r, hr, hrate, k0, hbooks⟩ :=
    RubikOBTM.Periodic.entropy_books_of_uniform_moments hT (fun _ => RubikOBTM.Finite.Intrinsic)
      (fun _ => RubikOBTM.Finite.nativeC) (fun _ => hC) RubikOBTM.Finite.periodicAct
      θ ρ hQ hθ0 hθ1 hρ0 hρ1 hmoment η hη
  refine ⟨L, r, k0, hL, dvd_trans (dvd_mul_right 4 RubikOBTM.Finite.period) hLT, hr, ?_, ?_⟩
  · rw [← hcard]
    exact hrate.le
  · intro hT' k hk
    obtain ⟨B, hcover, _, hsize⟩ := hbooks k hk
    exact ⟨B, hcover, hsize⟩
