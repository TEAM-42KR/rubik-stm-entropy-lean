import RubikSTM.Proofs.GlobalWords.ExceptionalPreprocessing
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikGlobalWord.exceptional_preprocessing :
    ∃ C : ℕ, ∀ (n : ℕ) (c : Rubik.Position n),
  ∃ w : List (Rubik.Move n),
    w.length ≤ RubikCore.cleanupBound + C*(3*Fintype.card (RubikGlobal.I n)) ∧
    ∀ s : Rubik.Sticker n, RubikGlobalWord.Nongeneric s →
      Rubik.applyWord w c.val s = Rubik.solved n s :=
  @proof_RubikGlobalWord_exceptional_preprocessing
