import RubikSTM.Proofs.WordBounds.ActualHd
import RubikSTM.Definitions.WordBounds.CostEnvelope
set_option autoImplicit false

theorem RubikCostBridge.actual_hd :
    ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ,
    Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∃ C : ℝ,
    ∀ᶠ n : ℕ in Filter.atTop,
      RubikCostBridge.d n ≤
        (Real.log (RubikCostBridge.q ^ 2) + η + e n) * RubikCostBridge.m n ^ 2 /
          (2 * Real.log (RubikCostBridge.m n / RubikCostBridge.h n)) +
        C * (RubikCostBridge.m n ^ 2 / RubikCostBridge.h n + RubikCostBridge.m n) :=
  @proof_RubikCostBridge_actual_hd
