import RubikSTM.Proofs.Bands.SameAxisFourth
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.sameAxisFourth :
    ∀ {n : ℕ} (q : Rubik.Axis) (ls : List (Fin n)), ((ls.map (Rubik.sliceQuarter n q)).reverse.prod) ^ 4 = 1 :=
  @proof_RubikBand_sameAxisFourth
