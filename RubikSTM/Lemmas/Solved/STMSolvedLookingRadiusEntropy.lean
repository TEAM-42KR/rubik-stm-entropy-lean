import RubikSTM.Proofs.Solved.STMSolvedLookingRadiusEntropy
import RubikSTM.Definitions.Solved.NormalizedMetrics
set_option autoImplicit false

theorem RubikSolved.STMSolvedLookingRadiusEntropy :
    Filter.Tendsto Rubik.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikSolved_STMSolvedLookingRadiusEntropy
