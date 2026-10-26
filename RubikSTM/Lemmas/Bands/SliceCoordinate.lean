import RubikSTM.Proofs.Bands.SliceCoordinate
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.sliceCoordinate :
    ∀ {n : ℕ} (q : Rubik.Axis) (l : Fin n) (s : Rubik.Sticker n), Rubik.coordinate (Rubik.sliceQuarter n q l s).val.1 q = Rubik.coordinate s.val.1 q :=
  @proof_RubikBand_sliceCoordinate
