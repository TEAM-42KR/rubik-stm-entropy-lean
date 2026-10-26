import RubikSTM.Proofs.Core.MatchCorePointwise
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikCore.match_core_pointwise :
    ∀ {n : ℕ} (c d : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ RubikCore.cleanupBound ∧ ∀ s : Rubik.Sticker n, RubikCore.IsCore s → Rubik.applyWord w c.val s = d.val s :=
  @proof_RubikCore_match_core_pointwise
