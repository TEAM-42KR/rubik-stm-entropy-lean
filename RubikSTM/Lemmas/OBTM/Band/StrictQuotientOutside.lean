import RubikSTM.Proofs.OBTM.Band.StrictQuotientOutside
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.strict_quotient_outside :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (w z : List (Rubik.Move n)) (hw : RubikBand.StrictControl a w) (hz : RubikBand.StrictControl a z) (s : Rubik.Sticker n) (hs : s ∉ RubikOBTM.Band.PairedRange a u v), ((RubikBand.wordPerm w * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm w)⁻¹) * (RubikBand.wordPerm z * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm z)⁻¹)⁻¹) s = s :=
  @proof_RubikOBTM_Band_strict_quotient_outside
