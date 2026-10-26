import RubikSTM.Proofs.OBTM.OBTMSharpDiameter
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.OBTMSharpDiameter :
    Filter.Tendsto RubikOBTM.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikOBTM_OBTMSharpDiameter
