import RubikSTM.Proofs.GlobalWords.Exceptional.CoreOutsideBand
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.core_outside_band :
    ∀ {n : ℕ} (i : RubikGlobal.I n) (s : Rubik.Sticker n) (hs : RubikCore.IsCore s), ¬ RubikBand.Band (RubikGlobal.depth i) s :=
  @proof_RubikGlobalWord_Exceptional_core_outside_band
