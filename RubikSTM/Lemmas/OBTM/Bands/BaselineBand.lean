import RubikSTM.Proofs.OBTM.Bands.BaselineBand
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem RubikBand.baselineBand :
    ∀ {n : ℕ} (a : Fin n) (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n), RubikBand.Band a (RubikBand.parallelBaseline q Y s) ↔ RubikBand.Band a s :=
  @proof_RubikBand_baselineBand
