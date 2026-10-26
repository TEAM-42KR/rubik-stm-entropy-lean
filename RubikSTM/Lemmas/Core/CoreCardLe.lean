import RubikSTM.Proofs.Core.CoreCardLe
import RubikSTM.Definitions.Core.Project
set_option autoImplicit false

theorem RubikCore.core_card_le :
    ∀ (n : ℕ), Fintype.card (RubikCore.CoreSticker n) ≤ 162 :=
  @proof_RubikCore_core_card_le
