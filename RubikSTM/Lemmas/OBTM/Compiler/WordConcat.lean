import RubikSTM.Proofs.OBTM.Compiler.WordConcat
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativePhaseModel
set_option autoImplicit false

theorem RubikOBTMCompiler.word_concat :
    ∀ {n : ℕ} (ws : List (List (RubikOBTM.BlockMove n))), RubikOBTM.Band.wordPerm ws.flatten=(ws.map RubikOBTM.Band.wordPerm).reverse.prod ∧
    ws.flatten.length=(ws.map List.length).sum :=
  @proof_RubikOBTMCompiler_word_concat
