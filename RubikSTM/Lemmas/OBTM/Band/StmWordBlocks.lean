import RubikSTM.Proofs.OBTM.Band.StmWordBlocks
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.stm_word_blocks :
    ∀ {n : ℕ} (hn : 2 ≤ n) (ms : List (Rubik.Move n)), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ 2*ms.length ∧ RubikOBTM.Band.wordPerm w = RubikBand.wordPerm ms :=
  @proof_RubikOBTM_Band_stm_word_blocks
