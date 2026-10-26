import RubikSTM.Lemmas.Asymptotics.LowerTail
import RubikSTM.Lemmas.Asymptotics.UpperTail
set_option autoImplicit false

theorem proof_RubikConstruction_EntropySharpDiameter : Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [RubikAsymptotics.lowerTail (ε / 2) (half_pos hε), RubikAsymptotics.upperTail (ε / 2) (half_pos hε)] with n hn₁ hn₂
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
