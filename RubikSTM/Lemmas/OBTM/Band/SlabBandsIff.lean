import RubikSTM.Proofs.OBTM.Band.SlabBandsIff
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.slab_bands_iff :
    ∀ {n : ℕ} (u v : Fin n) (s : Rubik.Sticker n), RubikBand.Bands (RubikOBTM.Band.slabDepths u v) s ↔ RubikOBTM.Band.ColumnBand u v s :=
  @proof_RubikOBTM_Band_slab_bands_iff
