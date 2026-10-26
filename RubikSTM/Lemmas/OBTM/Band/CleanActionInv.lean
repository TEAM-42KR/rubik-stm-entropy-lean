import RubikSTM.Proofs.OBTM.Band.CleanActionInv
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.clean_action_inv :
    ∀ {n : ℕ} (a u v : Fin n) (p : RubikOBTM.Band.PairPerm) (P : Equiv.Perm (Rubik.Sticker n)) (hp : RubikOBTM.Band.CleanAction a u v p P), RubikOBTM.Band.CleanAction a u v p⁻¹ P⁻¹ :=
  @proof_RubikOBTM_Band_clean_action_inv
