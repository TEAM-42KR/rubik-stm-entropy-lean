import RubikSTM.Proofs.OBTM.Global.ApplyBlockWordAppend
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.Global.applyBlockWord_append :
    ∀ {n : ℕ} (u v : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n), RubikOBTM.applyBlockWord (u ++ v) c = RubikOBTM.applyBlockWord v (RubikOBTM.applyBlockWord u c) :=
  @proof_RubikOBTM_Global_applyBlockWord_append
