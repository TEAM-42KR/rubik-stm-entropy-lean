import RubikSTM.Proofs.Solved.STMSolvedRadiusEntropy
import RubikSTM.Definitions.Solved.NormalizedMetrics
set_option autoImplicit false

theorem RubikSolved.STMSolvedRadiusEntropy :
    Filter.Tendsto Rubik.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikSolved_STMSolvedRadiusEntropy
