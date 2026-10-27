import RubikSTM.Proofs.Solved.OBTMSolvedLookingRadiusEntropy
import RubikSTM.Definitions.Solved.NormalizedMetrics
set_option autoImplicit false

theorem RubikSolved.OBTMSolvedLookingRadiusEntropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikSolved_OBTMSolvedLookingRadiusEntropy
