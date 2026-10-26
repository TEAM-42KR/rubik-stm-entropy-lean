import RubikSTM.Proofs.OBTM.SliceWordToBlocks
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.sliceWord_to_blocks :
    ∀ {n : ℕ} (hn : 2 ≤ n) (w : List (Rubik.Move n)), ∃ v : List (RubikOBTM.BlockMove n), v.length ≤ 2 * w.length ∧ ∀ c : Rubik.Colouring n, RubikOBTM.applyBlockWord v c = Rubik.applyWord w c :=
  @proof_RubikOBTM_sliceWord_to_blocks
