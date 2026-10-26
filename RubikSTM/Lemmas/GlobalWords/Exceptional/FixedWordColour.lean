import RubikSTM.Proofs.GlobalWords.Exceptional.FixedWordColour
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.fixed_word_colour :
    ∀ {n : ℕ} (w : List (Rubik.Move n)) (c : Rubik.Colouring n) (s : Rubik.Sticker n) (h : RubikBand.wordPerm w s = s), Rubik.applyWord w c s = c s :=
  @proof_RubikGlobalWord_Exceptional_fixed_word_colour
