import RubikSTM.Proofs.OBTM.Band.NativeWordInverse
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.native_word_inverse :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)), ∃ z : List (RubikOBTM.BlockMove n), z.length = w.length ∧ RubikOBTM.Band.wordPerm z = (RubikOBTM.Band.wordPerm w)⁻¹ :=
  @proof_RubikOBTM_Band_native_word_inverse
