import RubikSTM.Proofs.WordBounds.ActualCostEnvelope
import RubikSTM.Definitions.WordBounds.CostEnvelope
set_option autoImplicit false

theorem RubikCostBridge.actual_cost_envelope :
    RubikCostBridge.CostEnvelope :=
  @proof_RubikCostBridge_actual_cost_envelope
