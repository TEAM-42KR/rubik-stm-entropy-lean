import RubikSTM.Definitions.Solved.NormalizedMetrics
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OBTM.ReachableEntropy
import RubikSTM.Lemmas.Solved.obtm_radius_card_le
import RubikSTM.Lemmas.Solved.radius_comparison
import RubikSTM.Lemmas.OBTM.ObtmGraphConnected
import RubikSTM.Lemmas.Solved.entropy_of_counting_upper
import RubikSTM.Lemmas.OBTM.OBTMSharpDiameter
set_option autoImplicit false
open Filter Topology

theorem proof_RubikSolved_OBTMSolvedLookingRadiusEntropy : Filter.Tendsto RubikOBTM.normalizedSolvedLookingRadius Filter.atTop
    (nhds Rubik.entropyConstant) := by
  change Tendsto (fun n : ℕ => (RubikOBTM.solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2)
    atTop (nhds Rubik.entropyConstant)
  have hq : 1 ≤ RubikGeometry.orbitColourings := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hqcast : (RubikGeometry.orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ)^6 := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hcount : ∀ᶠ n : ℕ in atTop,
      RubikGeometry.orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤
        (18 * n + 1) ^ (RubikOBTM.solvedLookingRadius n + 6) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact (RubikOBTM.ReachableEntropy n).trans (RubikSolved.obtm_radius_card_le hn)
  have hu : Tendsto RubikOBTM.normalizedDiameter atTop
      (nhds ((1 / 4 : ℝ) * Real.log (RubikGeometry.orbitColourings : ℝ))) := by
    simpa only [hqcast, Rubik.entropyConstant] using RubikOBTM.OBTMSharpDiameter
  have hle : ∀ᶠ n : ℕ in atTop,
      (RubikOBTM.solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 ≤
        RubikOBTM.normalizedDiameter n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hc := RubikSolved.radius_comparison (RubikOBTM.obtmGraph n) (RubikOBTM.obtmGraph_connected hn)
    have hr : RubikOBTM.solvedLookingRadius n ≤ RubikOBTM.obtmDiameter n := hc.1.trans hc.2
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hl) (sq_nonneg _)
  simpa only [RubikOBTM.normalizedSolvedLookingRadius, hqcast, Rubik.entropyConstant] using
    RubikSolved.entropy_of_counting_upper RubikGeometry.orbitColourings 18 6 hq (by norm_num)
      RubikOBTM.solvedLookingRadius RubikOBTM.normalizedDiameter hcount hu hle
