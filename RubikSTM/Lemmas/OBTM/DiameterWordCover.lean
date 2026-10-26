import RubikSTM.Proofs.OBTM.DiameterWordCover
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.diameter_word_cover :
    ∀ {n : ℕ} (hn : 2 ≤ n) (v : Rubik.Position n), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ RubikOBTM.obtmDiameter n ∧ RubikOBTM.applyBlockWord w (Rubik.solved n) = v.val :=
  @proof_RubikOBTM_diameter_word_cover
