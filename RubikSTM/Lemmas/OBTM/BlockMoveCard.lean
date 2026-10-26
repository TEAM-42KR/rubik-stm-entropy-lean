import RubikSTM.Proofs.OBTM.BlockMoveCard
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockMove_card :
    ∀ (n : ℕ), Fintype.card (RubikOBTM.BlockMove n) = 18 * (n - 1) :=
  @proof_RubikOBTM_blockMove_card
