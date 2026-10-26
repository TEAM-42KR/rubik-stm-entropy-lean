import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.OBTM.Compiler.NativeInverseWord
set_option autoImplicit false

theorem proof_RubikOBTM_Band_native_word_inverse {n : ℕ} (w : List (RubikOBTM.BlockMove n)) :
    ∃ z : List (RubikOBTM.BlockMove n), z.length = w.length ∧
      RubikOBTM.Band.wordPerm z = (RubikOBTM.Band.wordPerm w)⁻¹ :=
  RubikOBTMCompiler.native_inverse_word w
