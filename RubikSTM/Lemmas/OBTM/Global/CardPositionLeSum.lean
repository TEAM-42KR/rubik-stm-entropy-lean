import RubikSTM.Proofs.OBTM.Global.CardPositionLeSum
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.Global.card_position_le_sum :
    ∀ {n : ℕ} (hn : 2 ≤ n), Fintype.card (Rubik.Position n) ≤ ∑ j ∈ Finset.range (RubikOBTM.obtmDiameter n + 1), (18 * (n - 1)) ^ j :=
  @proof_RubikOBTM_Global_card_position_le_sum
