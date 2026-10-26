import RubikSTM.Proofs.GlobalWords.GlobalCover
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.global_cover :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (s : Rubik.Sticker n), RubikGlobalWord.Nongeneric s ∨ ∃ t : RubikGlobalWord.Task f, s ∈ RubikGlobalWord.Region f t :=
  @proof_RubikGlobalWord_global_cover
