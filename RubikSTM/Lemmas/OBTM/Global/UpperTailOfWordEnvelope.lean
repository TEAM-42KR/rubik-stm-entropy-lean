import RubikSTM.Proofs.OBTM.Global.UpperTailOfWordEnvelope
import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
set_option autoImplicit false

theorem RubikOBTM.Global.upperTail_of_wordEnvelope :
    ∀ (hcost : RubikOBTM.Global.WordCostEnvelope) (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, RubikOBTM.normalizedDiameter n ≤ Rubik.entropyConstant + ε :=
  @proof_RubikOBTM_Global_upperTail_of_wordEnvelope
