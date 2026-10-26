import RubikSTM.Proofs.OBTM.BlockInverse
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.block_inverse :
    ∀ {n : ℕ} (m : RubikOBTM.BlockMove n), ∃ r : RubikOBTM.BlockMove n, RubikOBTM.blockPermutation r = (RubikOBTM.blockPermutation m)⁻¹ :=
  @proof_RubikOBTM_block_inverse
