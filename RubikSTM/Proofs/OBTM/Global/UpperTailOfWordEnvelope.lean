import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
import RubikSTM.Definitions.WordBounds.CostEnvelope
import RubikSTM.Lemmas.OBTM.Global.WordEnvelopeHd
import RubikSTM.Lemmas.Asymptotics.CostBridgeQIdentity
import RubikSTM.Lemmas.GlobalRates.PairedRectangleEnvelope
set_option autoImplicit false

theorem proof_RubikOBTM_Global_upperTail_of_wordEnvelope (hcost : RubikOBTM.Global.WordCostEnvelope) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in Filter.atTop,
    RubikOBTM.normalizedDiameter n ≤ Rubik.entropyConstant + ε := by
  refine (RubikGlobalRates.paired_rectangle_envelope RubikCostBridge.q (fun n => (RubikOBTM.obtmDiameter n : ℝ))
    RubikCostBridge.m RubikCostBridge.h (fun n => ?_) (fun n => rfl)
    (RubikOBTM.Global.wordEnvelope_hd hcost) ε hε).mono ?_
  · show ((RubikCostBridge.mNat n : ℕ) : ℝ) = ((n / 2 - 1 : ℕ) : ℝ)
    congr 1
    show (n - 2) / 2 = n / 2 - 1
    omega
  · intro n hn
    rw [← RubikAsymptotics.costBridge_q_identity]
    exact hn
