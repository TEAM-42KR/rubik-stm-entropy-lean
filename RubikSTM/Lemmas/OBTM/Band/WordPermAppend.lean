import RubikSTM.Proofs.OBTM.Band.WordPermAppend
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.wordPerm_append :
    ∀ {n : ℕ} (w z : List (RubikOBTM.BlockMove n)), RubikOBTM.Band.wordPerm (w ++ z) = RubikOBTM.Band.wordPerm z * RubikOBTM.Band.wordPerm w :=
  @proof_RubikOBTM_Band_wordPerm_append
