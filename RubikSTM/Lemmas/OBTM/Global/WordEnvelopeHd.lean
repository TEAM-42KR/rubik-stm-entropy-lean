import RubikSTM.Proofs.OBTM.Global.WordEnvelopeHd
import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
set_option autoImplicit false

theorem RubikOBTM.Global.wordEnvelope_hd :
    ∀ (hcost : RubikOBTM.Global.WordCostEnvelope), ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, (RubikOBTM.obtmDiameter n : ℝ) ≤ (Real.log (RubikCostBridge.q ^ 2) + η + e n) * RubikCostBridge.m n ^ 2 / (2 * Real.log (RubikCostBridge.m n / RubikCostBridge.h n)) + C * (RubikCostBridge.m n ^ 2 / RubikCostBridge.h n + RubikCostBridge.m n) :=
  @proof_RubikOBTM_Global_wordEnvelope_hd
