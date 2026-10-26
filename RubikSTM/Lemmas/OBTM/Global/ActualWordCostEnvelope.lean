import RubikSTM.Proofs.OBTM.Global.ActualWordCostEnvelope
import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
set_option autoImplicit false

theorem RubikOBTM.Global.actual_word_cost_envelope :
    RubikOBTM.Global.WordCostEnvelope :=
  @proof_RubikOBTM_Global_actual_word_cost_envelope
