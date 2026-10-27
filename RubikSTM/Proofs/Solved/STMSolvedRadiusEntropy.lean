import RubikSTM.Definitions.Solved.NormalizedMetrics
import RubikSTM.Lemmas.Solved.STMSolvedLookingRadiusEntropy
import RubikSTM.Lemmas.Solved.radius_comparison
import RubikSTM.Lemmas.SolvedSupport.Rubik_stmGraph_connected
import RubikSTM.Lemmas.Construction.EntropySharpDiameter
set_option autoImplicit false
open Filter Topology

theorem proof_RubikSolved_STMSolvedRadiusEntropy : Filter.Tendsto Rubik.normalizedSolvedRadius Filter.atTop
    (nhds Rubik.entropyConstant) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    RubikSolved.STMSolvedLookingRadiusEntropy
    RubikConstruction.EntropySharpDiameter
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hc := RubikSolved.radius_comparison (Rubik.stmGraph n) (Rubik.stmGraph_connected n)
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc.1) hl) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hc := RubikSolved.radius_comparison (Rubik.stmGraph n) (Rubik.stmGraph_connected n)
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc.2) hl) (sq_nonneg _)
