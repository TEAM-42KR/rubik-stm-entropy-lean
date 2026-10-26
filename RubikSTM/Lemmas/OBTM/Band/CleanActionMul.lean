import RubikSTM.Proofs.OBTM.Band.CleanActionMul
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.clean_action_mul :
    ∀ {n : ℕ} (a u v : Fin n) (p q : RubikOBTM.Band.PairPerm) (P Q : Equiv.Perm (Rubik.Sticker n)) (hp : RubikOBTM.Band.CleanAction a u v p P) (hq : RubikOBTM.Band.CleanAction a u v q Q), RubikOBTM.Band.CleanAction a u v (p*q) (P*Q) :=
  @proof_RubikOBTM_Band_clean_action_mul
