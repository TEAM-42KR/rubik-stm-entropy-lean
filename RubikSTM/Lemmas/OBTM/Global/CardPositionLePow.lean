import RubikSTM.Proofs.OBTM.Global.CardPositionLePow
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.Global.card_position_le_pow :
    ∀ {n : ℕ} (hn : 2 ≤ n), Fintype.card (Rubik.Position n) ≤ (18 * (n - 1) + 1) ^ RubikOBTM.obtmDiameter n :=
  @proof_RubikOBTM_Global_card_position_le_pow
