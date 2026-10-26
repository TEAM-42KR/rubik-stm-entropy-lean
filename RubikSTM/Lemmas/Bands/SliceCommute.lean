import RubikSTM.Proofs.Bands.SliceCommute
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.sliceCommute :
    ∀ {n : ℕ} (q : Rubik.Axis) (b c : Fin n), Commute (Rubik.sliceQuarter n q b) (Rubik.sliceQuarter n q c) :=
  @proof_RubikBand_sliceCommute
