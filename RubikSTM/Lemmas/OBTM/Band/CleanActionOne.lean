import RubikSTM.Proofs.OBTM.Band.CleanActionOne
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.clean_action_one :
    ∀ {n : ℕ} (a u v : Fin n), RubikOBTM.Band.CleanAction a u v 1 1 :=
  @proof_RubikOBTM_Band_clean_action_one
