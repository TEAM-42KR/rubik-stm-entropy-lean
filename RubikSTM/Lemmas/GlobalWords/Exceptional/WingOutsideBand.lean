import RubikSTM.Proofs.GlobalWords.Exceptional.WingOutsideBand
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.wing_outside_band :
    ∀ {n : ℕ} (i j : RubikGlobal.I n) (hij : i ≠ j) (s : Rubik.Sticker n) (hs : s ∈ RubikGlobal.WingRange j), ¬ RubikBand.Band (RubikGlobal.depth i) s :=
  @proof_RubikGlobalWord_Exceptional_wing_outside_band
