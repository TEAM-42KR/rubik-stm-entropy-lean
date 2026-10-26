import RubikSTM.Proofs.GlobalWords.RegionSame
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.region_same :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobalWord.SamePair f), RubikGlobalWord.Region f (Sum.inr p) = RubikGlobal.GenericRange p.val :=
  @proof_RubikGlobalWord_region_same
