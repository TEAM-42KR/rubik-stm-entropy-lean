import RubikSTM.Proofs.OBTM.WordBounds.RowCeilEqNatCeil
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikCostBridge.rowCeil_eq_natCeil :
    ∀ (r k : ℕ) (hk : 0 < k), RubikRectangle.rowCeil r k = ⌈(r : ℝ) / (k : ℝ)⌉₊ :=
  @proof_RubikCostBridge_rowCeil_eq_natCeil
