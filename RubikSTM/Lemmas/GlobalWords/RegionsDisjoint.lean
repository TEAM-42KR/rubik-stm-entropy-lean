import RubikSTM.Proofs.GlobalWords.RegionsDisjoint
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.regions_disjoint :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (t u : RubikGlobalWord.Task f)
  (hne : t ≠ u), Disjoint (RubikGlobalWord.Region f t) (RubikGlobalWord.Region f u) :=
  @proof_RubikGlobalWord_regions_disjoint
