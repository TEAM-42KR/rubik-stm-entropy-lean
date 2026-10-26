import RubikSTM.Proofs.GlobalWords.RegionRectangle
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.region_rectangle :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (r : RubikGlobalWord.GroupPair h), RubikGlobalWord.Region f (Sum.inl r) =
    {s | RubikPayload.Rectangles (RubikGlobalWord.depthGroup f r.val.1)
      (RubikGlobalWord.depthGroup f r.val.2) s} :=
  @proof_RubikGlobalWord_region_rectangle
