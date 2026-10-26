import RubikSTM.Definitions.Geometry.StmGraph
import RubikSTM.Definitions.WordBounds.CostEnvelope
import RubikSTM.Lemmas.WordBounds.ActualHd
import RubikSTM.Lemmas.Asymptotics.CostBridgeQIdentity
import RubikSTM.Lemmas.GlobalRates.PairedRectangleEnvelope
set_option autoImplicit false

theorem proof_RubikAsymptotics_upperTail (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in Filter.atTop,
    Rubik.normalizedDiameter n ≤ Rubik.entropyConstant + ε := by
  refine (RubikGlobalRates.paired_rectangle_envelope RubikCostBridge.q RubikCostBridge.d
    RubikCostBridge.m RubikCostBridge.h (fun n => ?_) (fun n => rfl)
    RubikCostBridge.actual_hd ε hε).mono ?_
  · show ((RubikCostBridge.mNat n : ℕ) : ℝ) = ((n / 2 - 1 : ℕ) : ℝ)
    congr 1
    show (n - 2) / 2 = n / 2 - 1
    omega
  · intro n hn
    rw [← RubikAsymptotics.costBridge_q_identity]
    exact hn
