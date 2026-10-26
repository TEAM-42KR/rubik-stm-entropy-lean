import RubikSTM.Proofs.OBTM.BlockSliceWordAction
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockSliceWord_action :
    ∀ {n : ℕ} (m : RubikOBTM.BlockMove n) (c : Rubik.Colouring n), Rubik.applyWord (RubikOBTM.blockSliceWord m) c = RubikOBTM.applyBlock m c :=
  @proof_RubikOBTM_blockSliceWord_action
