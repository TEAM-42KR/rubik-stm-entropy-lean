import RubikSTM.Proofs.Core.CleanupToSolved
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikCore.cleanup_to_solved :
    ∀ {n : ℕ} (c : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ RubikCore.cleanupBound ∧ ∀ s : Rubik.Sticker n, RubikCore.IsCore s → Rubik.applyWord w c.val s = Rubik.solved n s :=
  @proof_RubikCore_cleanup_to_solved
