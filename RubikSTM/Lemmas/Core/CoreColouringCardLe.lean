import RubikSTM.Proofs.Core.CoreColouringCardLe
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
open scoped Classical

theorem RubikCore.coreColouring_card_le :
    ∀ (n : ℕ), Fintype.card (RubikCore.CoreColouring n) ≤ RubikCore.cleanupBound :=
  @proof_RubikCore_coreColouring_card_le
