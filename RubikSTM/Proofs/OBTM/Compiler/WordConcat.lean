import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativePhaseModel
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_word_concat {n : ℕ} (ws : List (List (RubikOBTM.BlockMove n))) :
  RubikOBTM.Band.wordPerm ws.flatten=(ws.map RubikOBTM.Band.wordPerm).reverse.prod ∧
    ws.flatten.length=(ws.map List.length).sum := by
  induction ws with
  | nil => simp [RubikOBTM.Band.wordPerm]
  | cons w ws ih =>
    constructor
    · simp only [List.flatten_cons,List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,
        RubikOBTM.Band.wordPerm_append,ih.1]
    · simp [ih.2]

#print axioms proof_RubikOBTMCompiler_word_concat
