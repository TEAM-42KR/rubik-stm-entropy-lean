import RubikSTM.Proofs.OBTM.BlockWordAction
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockWord_action :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n), RubikOBTM.applyBlockWord w c = fun s => c (((w.map RubikOBTM.blockPermutation).reverse.prod)⁻¹ s) :=
  @proof_RubikOBTM_blockWord_action
