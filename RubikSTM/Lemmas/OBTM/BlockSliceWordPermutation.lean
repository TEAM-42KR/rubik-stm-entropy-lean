import RubikSTM.Proofs.OBTM.BlockSliceWordPermutation
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockSliceWord_permutation :
    ∀ {n : ℕ} (m : RubikOBTM.BlockMove n), (((RubikOBTM.blockSliceWord m).map Rubik.movePermutation).reverse.prod) = RubikOBTM.blockPermutation m :=
  @proof_RubikOBTM_blockSliceWord_permutation
