import RubikSTM.Proofs.OBTM.WordBounds.EventuallyBlockLarge
import RubikSTM.Definitions.WordBounds.CostEnvelope
set_option autoImplicit false

theorem RubikCostBridge.eventually_block_large :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ), ∀ᶠ n : ℕ in Filter.atTop, 0 < RubikCostBridge.hNat n ∧
    ∀ s : ℕ, RubikCostBridge.mNat n / RubikCostBridge.hNat n ≤ s →
      max K 1 ≤ RubikCostBridge.block ρ s :=
  @proof_RubikCostBridge_eventually_block_large
