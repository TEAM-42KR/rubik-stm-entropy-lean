import RubikSTM.Proofs.GlobalWords.UndoWord
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.undo_word :
    ∀ {n : ℕ} (w : List (Rubik.Move n)) (c : Rubik.Colouring n), Rubik.applyWord (RubikPayload.inverseWord w) (Rubik.applyWord w c) = c :=
  @proof_RubikGlobalWord_undo_word
