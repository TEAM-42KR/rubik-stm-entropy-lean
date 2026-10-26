import RubikSTM.Proofs.OBTM.Bands.BaselineOutside
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.baselineOutside :
    ∀ {n : ℕ} (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n) (hs : ¬ RubikBand.Bands Y s), RubikBand.parallelBaseline q Y s = s :=
  @proof_RubikBand_baselineOutside
