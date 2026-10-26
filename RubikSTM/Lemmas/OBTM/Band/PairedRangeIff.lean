import RubikSTM.Proofs.OBTM.Band.PairedRangeIff
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.paired_range_iff :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (s : Rubik.Sticker n), s ∈ RubikOBTM.Band.PairedRange a u v ↔ RubikBand.Band a s ∧ RubikOBTM.Band.ColumnBand u v s :=
  @proof_RubikOBTM_Band_paired_range_iff
