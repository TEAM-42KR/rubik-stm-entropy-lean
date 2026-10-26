import RubikSTM.Proofs.Core.MatchReachableCore
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikCore.match_reachable_core :
    ∀ {n : ℕ} (c d : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ RubikCore.cleanupBound ∧ RubikCore.project (Rubik.applyWord w c.val) = RubikCore.project d.val :=
  @proof_RubikCore_match_reachable_core
