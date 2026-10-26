import RubikSTM.Proofs.Asymptotics.CostBridgeQIdentity
import RubikSTM.Definitions.Geometry.StmGraph
import RubikSTM.Definitions.WordBounds.CostEnvelope
set_option autoImplicit false

theorem RubikAsymptotics.costBridge_q_identity :
    Real.log RubikCostBridge.q / 4 = Rubik.entropyConstant :=
  @proof_RubikAsymptotics_costBridge_q_identity
