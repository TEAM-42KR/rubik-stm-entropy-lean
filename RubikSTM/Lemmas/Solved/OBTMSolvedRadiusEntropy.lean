import RubikSTM.Proofs.Solved.OBTMSolvedRadiusEntropy
import RubikSTM.Definitions.Solved.NormalizedMetrics
set_option autoImplicit false

theorem RubikSolved.OBTMSolvedRadiusEntropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikSolved_OBTMSolvedRadiusEntropy
