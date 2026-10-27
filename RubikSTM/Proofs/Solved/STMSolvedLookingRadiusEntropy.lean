import RubikSTM.Definitions.Solved.NormalizedMetrics
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OBTM.ReachableEntropy
import RubikSTM.Lemmas.Solved.stm_radius_card_le
import RubikSTM.Lemmas.Solved.radius_comparison
import RubikSTM.Lemmas.SolvedSupport.Rubik_stmGraph_connected
import RubikSTM.Lemmas.Solved.entropy_of_counting_upper
import RubikSTM.Lemmas.Construction.EntropySharpDiameter
set_option autoImplicit false
open Filter Topology

theorem proof_RubikSolved_STMSolvedLookingRadiusEntropy : Filter.Tendsto Rubik.normalizedSolvedLookingRadius Filter.atTop
    (nhds Rubik.entropyConstant) := by
  change Tendsto (fun n : ℕ => (Rubik.solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2)
    atTop (nhds Rubik.entropyConstant)
  have hq : 1 ≤ RubikGeometry.orbitColourings := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hqcast : (RubikGeometry.orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ)^6 := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hcount : ∀ᶠ n : ℕ in atTop,
      RubikGeometry.orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤
        (9 * n + 1) ^ (Rubik.solvedLookingRadius n + 6) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact (RubikOBTM.ReachableEntropy n).trans (RubikSolved.stm_radius_card_le hn)
  have hu : Tendsto Rubik.normalizedDiameter atTop
      (nhds ((1 / 4 : ℝ) * Real.log (RubikGeometry.orbitColourings : ℝ))) := by
    simpa only [hqcast, Rubik.entropyConstant] using RubikConstruction.EntropySharpDiameter
  have hle : ∀ᶠ n : ℕ in atTop,
      (Rubik.solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 ≤
        Rubik.normalizedDiameter n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hc := RubikSolved.radius_comparison (Rubik.stmGraph n) (Rubik.stmGraph_connected n)
    have hr : Rubik.solvedLookingRadius n ≤ Rubik.diameter n := hc.1.trans hc.2
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hl) (sq_nonneg _)
  simpa only [Rubik.normalizedSolvedLookingRadius, hqcast, Rubik.entropyConstant] using
    RubikSolved.entropy_of_counting_upper RubikGeometry.orbitColourings 9 6 hq (by norm_num)
      Rubik.solvedLookingRadius Rubik.normalizedDiameter hcount hu hle
