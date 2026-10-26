import RubikSTM.Proofs.OBTM.SliceTwoBlocks
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.slice_two_blocks :
    ∀ {n : ℕ} (hn : 2 ≤ n) (m : Rubik.Move n), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ 2 ∧ ((w.map RubikOBTM.blockPermutation).reverse.prod) = Rubik.movePermutation m :=
  @proof_RubikOBTM_slice_two_blocks
